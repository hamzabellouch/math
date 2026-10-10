import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23168 raw23168Labels = mixedMoment B node3207 node3207Labels := by
  calc
    mixedMoment B raw23168 raw23168Labels = mixedMoment B raw23168step0 raw23168step0Labels := by
      have hz : ∀ j, raw23168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23168step0 = (fun i j => raw23168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23168step0 raw23168; decide +kernel
      have hl : raw23168step0Labels = raw23168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23168 raw23168Labels permutation346 hz
    mixedMoment B raw23168step0 raw23168step0Labels = mixedMoment B raw23168step1 raw23168step1Labels := by
      have ha : raw23168step1 = (fun i j => raw23168step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23168step1 raw23168step0; decide +kernel
      have hl : raw23168step1Labels = raw23168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23168step0 raw23168step0Labels permutation38 permutation3
    _ = mixedMoment B node3207 node3207Labels := by rfl

def raw23169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw23169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23169 raw23169Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw23169 raw23169Labels = mixedMoment B raw23169step0 raw23169step0Labels := by
      have hz : ∀ j, raw23169 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23169step0 = (fun i j => raw23169 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23169step0 raw23169; decide +kernel
      have hl : raw23169step0Labels = raw23169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23169 raw23169Labels permutation434 hz
    mixedMoment B raw23169step0 raw23169step0Labels = mixedMoment B raw23169step1 raw23169step1Labels := by
      have hz : ∀ j, raw23169step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23169step1 = (fun i j => raw23169step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23169step1 raw23169step0; decide +kernel
      have hl : raw23169step1Labels = raw23169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23169step0 raw23169step0Labels permutation80 hz
    mixedMoment B raw23169step1 raw23169step1Labels = mixedMoment B raw23169step2 raw23169step2Labels := by
      have ha : raw23169step2 = (fun i j => raw23169step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23169step2 raw23169step1; decide +kernel
      have hl : raw23169step2Labels = raw23169step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23169step1 raw23169step1Labels permutation9 permutation3
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw23170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23170step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23170 raw23170Labels = mixedMoment B node649 node649Labels := by
  calc
    mixedMoment B raw23170 raw23170Labels = mixedMoment B raw23170step0 raw23170step0Labels := by
      have hz : ∀ j, raw23170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23170step0 = (fun i j => raw23170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23170step0 raw23170; decide +kernel
      have hl : raw23170step0Labels = raw23170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23170 raw23170Labels permutation434 hz
    mixedMoment B raw23170step0 raw23170step0Labels = mixedMoment B raw23170step1 raw23170step1Labels := by
      have hz : ∀ j, raw23170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23170step1 = (fun i j => raw23170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23170step1 raw23170step0; decide +kernel
      have hl : raw23170step1Labels = raw23170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23170step0 raw23170step0Labels permutation80 hz
    mixedMoment B raw23170step1 raw23170step1Labels = mixedMoment B raw23170step2 raw23170step2Labels := by
      have ha : raw23170step2 = (fun i j => raw23170step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23170step2 raw23170step1; decide +kernel
      have hl : raw23170step2Labels = raw23170step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23170step1 raw23170step1Labels permutation8 permutation3
    _ = mixedMoment B node649 node649Labels := by rfl

def raw23171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23171 raw23171Labels = mixedMoment B node1344 node1344Labels := by
  calc
    mixedMoment B raw23171 raw23171Labels = mixedMoment B raw23171step0 raw23171step0Labels := by
      have hz : ∀ j, raw23171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23171step0 = (fun i j => raw23171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23171step0 raw23171; decide +kernel
      have hl : raw23171step0Labels = raw23171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23171 raw23171Labels permutation434 hz
    mixedMoment B raw23171step0 raw23171step0Labels = mixedMoment B raw23171step1 raw23171step1Labels := by
      have ha : raw23171step1 = (fun i j => raw23171step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23171step1 raw23171step0; decide +kernel
      have hl : raw23171step1Labels = raw23171step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23171step0 raw23171step0Labels permutation38 permutation3
    _ = mixedMoment B node1344 node1344Labels := by rfl

def raw23172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23172 raw23172Labels = mixedMoment B node1344 node1344Labels := by
  calc
    mixedMoment B raw23172 raw23172Labels = mixedMoment B raw23172step0 raw23172step0Labels := by
      have hz : ∀ j, raw23172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23172step0 = (fun i j => raw23172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23172step0 raw23172; decide +kernel
      have hl : raw23172step0Labels = raw23172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23172 raw23172Labels permutation346 hz
    mixedMoment B raw23172step0 raw23172step0Labels = mixedMoment B raw23172step1 raw23172step1Labels := by
      have ha : raw23172step1 = (fun i j => raw23172step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23172step1 raw23172step0; decide +kernel
      have hl : raw23172step1Labels = raw23172step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23172step0 raw23172step0Labels permutation38 permutation3
    _ = mixedMoment B node1344 node1344Labels := by rfl

def raw23173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23173 raw23173Labels = mixedMoment B node1447 node1447Labels := by
  calc
    mixedMoment B raw23173 raw23173Labels = mixedMoment B raw23173step0 raw23173step0Labels := by
      have hz : ∀ j, raw23173 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23173step0 = (fun i j => raw23173 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23173step0 raw23173; decide +kernel
      have hl : raw23173step0Labels = raw23173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23173 raw23173Labels permutation434 hz
    mixedMoment B raw23173step0 raw23173step0Labels = mixedMoment B raw23173step1 raw23173step1Labels := by
      have hz : ∀ j, raw23173step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23173step1 = (fun i j => raw23173step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23173step1 raw23173step0; decide +kernel
      have hl : raw23173step1Labels = raw23173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23173step0 raw23173step0Labels permutation80 hz
    mixedMoment B raw23173step1 raw23173step1Labels = mixedMoment B raw23173step2 raw23173step2Labels := by
      have ha : raw23173step2 = (fun i j => raw23173step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23173step2 raw23173step1; decide +kernel
      have hl : raw23173step2Labels = raw23173step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23173step1 raw23173step1Labels permutation9 permutation3
    _ = mixedMoment B node1447 node1447Labels := by rfl

def raw23174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23174 raw23174Labels = mixedMoment B node632 node632Labels := by
  calc
    mixedMoment B raw23174 raw23174Labels = mixedMoment B raw23174step0 raw23174step0Labels := by
      have hz : ∀ j, raw23174 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23174step0 = (fun i j => raw23174 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23174step0 raw23174; decide +kernel
      have hl : raw23174step0Labels = raw23174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23174 raw23174Labels permutation434 hz
    mixedMoment B raw23174step0 raw23174step0Labels = mixedMoment B raw23174step1 raw23174step1Labels := by
      have ha : raw23174step1 = (fun i j => raw23174step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23174step1 raw23174step0; decide +kernel
      have hl : raw23174step1Labels = raw23174step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23174step0 raw23174step0Labels permutation32 permutation3
    _ = mixedMoment B node632 node632Labels := by rfl

def raw23175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23175 raw23175Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw23175 raw23175Labels = mixedMoment B raw23175step0 raw23175step0Labels := by
      have hz : ∀ j, raw23175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23175step0 = (fun i j => raw23175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23175step0 raw23175; decide +kernel
      have hl : raw23175step0Labels = raw23175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23175 raw23175Labels permutation434 hz
    mixedMoment B raw23175step0 raw23175step0Labels = mixedMoment B raw23175step1 raw23175step1Labels := by
      have ha : raw23175step1 = (fun i j => raw23175step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23175step1 raw23175step0; decide +kernel
      have hl : raw23175step1Labels = raw23175step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23175step0 raw23175step0Labels permutation32 permutation3
    _ = mixedMoment B node1322 node1322Labels := by rfl

def raw23176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23176 raw23176Labels = mixedMoment B node1331 node1331Labels := by
  calc
    mixedMoment B raw23176 raw23176Labels = mixedMoment B raw23176step0 raw23176step0Labels := by
      have ha : raw23176step0 = (fun i j => raw23176 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23176step0 raw23176; decide +kernel
      have hl : raw23176step0Labels = raw23176Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23176 raw23176Labels permutation200 permutation3
    _ = mixedMoment B node1331 node1331Labels := by rfl

def raw23177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23177 raw23177Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw23177 raw23177Labels = mixedMoment B raw23177step0 raw23177step0Labels := by
      have hz : ∀ j, raw23177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23177step0 = (fun i j => raw23177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23177step0 raw23177; decide +kernel
      have hl : raw23177step0Labels = raw23177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23177 raw23177Labels permutation434 hz
    mixedMoment B raw23177step0 raw23177step0Labels = mixedMoment B raw23177step1 raw23177step1Labels := by
      have ha : raw23177step1 = (fun i j => raw23177step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23177step1 raw23177step0; decide +kernel
      have hl : raw23177step1Labels = raw23177step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23177step0 raw23177step0Labels permutation36 permutation3
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw23178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23178 raw23178Labels = mixedMoment B node632 node632Labels := by
  calc
    mixedMoment B raw23178 raw23178Labels = mixedMoment B raw23178step0 raw23178step0Labels := by
      have hz : ∀ j, raw23178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23178step0 = (fun i j => raw23178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23178step0 raw23178; decide +kernel
      have hl : raw23178step0Labels = raw23178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23178 raw23178Labels permutation346 hz
    mixedMoment B raw23178step0 raw23178step0Labels = mixedMoment B raw23178step1 raw23178step1Labels := by
      have ha : raw23178step1 = (fun i j => raw23178step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23178step1 raw23178step0; decide +kernel
      have hl : raw23178step1Labels = raw23178step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23178step0 raw23178step0Labels permutation32 permutation3
    _ = mixedMoment B node632 node632Labels := by rfl

def raw23179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23179 raw23179Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw23179 raw23179Labels = mixedMoment B raw23179step0 raw23179step0Labels := by
      have hz : ∀ j, raw23179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23179step0 = (fun i j => raw23179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23179step0 raw23179; decide +kernel
      have hl : raw23179step0Labels = raw23179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23179 raw23179Labels permutation346 hz
    mixedMoment B raw23179step0 raw23179step0Labels = mixedMoment B raw23179step1 raw23179step1Labels := by
      have ha : raw23179step1 = (fun i j => raw23179step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23179step1 raw23179step0; decide +kernel
      have hl : raw23179step1Labels = raw23179step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23179step0 raw23179step0Labels permutation32 permutation3
    _ = mixedMoment B node1322 node1322Labels := by rfl

def raw23180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23180 raw23180Labels = mixedMoment B node1331 node1331Labels := by
  calc
    mixedMoment B raw23180 raw23180Labels = mixedMoment B raw23180step0 raw23180step0Labels := by
      have ha : raw23180step0 = (fun i j => raw23180 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23180step0 raw23180; decide +kernel
      have hl : raw23180step0Labels = raw23180Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23180 raw23180Labels permutation176 permutation3
    _ = mixedMoment B node1331 node1331Labels := by rfl

def raw23181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23181 raw23181Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw23181 raw23181Labels = mixedMoment B raw23181step0 raw23181step0Labels := by
      have hz : ∀ j, raw23181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23181step0 = (fun i j => raw23181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23181step0 raw23181; decide +kernel
      have hl : raw23181step0Labels = raw23181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23181 raw23181Labels permutation346 hz
    mixedMoment B raw23181step0 raw23181step0Labels = mixedMoment B raw23181step1 raw23181step1Labels := by
      have ha : raw23181step1 = (fun i j => raw23181step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23181step1 raw23181step0; decide +kernel
      have hl : raw23181step1Labels = raw23181step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23181step0 raw23181step0Labels permutation36 permutation3
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw23182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23182step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw23182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23182 raw23182Labels = mixedMoment B node635 node635Labels := by
  calc
    mixedMoment B raw23182 raw23182Labels = mixedMoment B raw23182step0 raw23182step0Labels := by
      have hz : ∀ j, raw23182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23182step0 = (fun i j => raw23182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23182step0 raw23182; decide +kernel
      have hl : raw23182step0Labels = raw23182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23182 raw23182Labels permutation434 hz
    mixedMoment B raw23182step0 raw23182step0Labels = mixedMoment B raw23182step1 raw23182step1Labels := by
      have hz : ∀ j, raw23182step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23182step1 = (fun i j => raw23182step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23182step1 raw23182step0; decide +kernel
      have hl : raw23182step1Labels = raw23182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23182step0 raw23182step0Labels permutation80 hz
    mixedMoment B raw23182step1 raw23182step1Labels = mixedMoment B raw23182step2 raw23182step2Labels := by
      have ha : raw23182step2 = (fun i j => raw23182step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23182step2 raw23182step1; decide +kernel
      have hl : raw23182step2Labels = raw23182step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23182step1 raw23182step1Labels permutation9 permutation3
    _ = mixedMoment B node635 node635Labels := by rfl

def raw23183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23183step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw23183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23183 raw23183Labels = mixedMoment B node1324 node1324Labels := by
  calc
    mixedMoment B raw23183 raw23183Labels = mixedMoment B raw23183step0 raw23183step0Labels := by
      have hz : ∀ j, raw23183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23183step0 = (fun i j => raw23183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23183step0 raw23183; decide +kernel
      have hl : raw23183step0Labels = raw23183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23183 raw23183Labels permutation434 hz
    mixedMoment B raw23183step0 raw23183step0Labels = mixedMoment B raw23183step1 raw23183step1Labels := by
      have hz : ∀ j, raw23183step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23183step1 = (fun i j => raw23183step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23183step1 raw23183step0; decide +kernel
      have hl : raw23183step1Labels = raw23183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23183step0 raw23183step0Labels permutation80 hz
    mixedMoment B raw23183step1 raw23183step1Labels = mixedMoment B raw23183step2 raw23183step2Labels := by
      have ha : raw23183step2 = (fun i j => raw23183step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23183step2 raw23183step1; decide +kernel
      have hl : raw23183step2Labels = raw23183step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23183step1 raw23183step1Labels permutation9 permutation3
    _ = mixedMoment B node1324 node1324Labels := by rfl

def raw23184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw23184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23184 raw23184Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw23184 raw23184Labels = mixedMoment B raw23184step0 raw23184step0Labels := by
      have hz : ∀ j, raw23184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23184step0 = (fun i j => raw23184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23184step0 raw23184; decide +kernel
      have hl : raw23184step0Labels = raw23184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23184 raw23184Labels permutation434 hz
    mixedMoment B raw23184step0 raw23184step0Labels = mixedMoment B raw23184step1 raw23184step1Labels := by
      have ha : raw23184step1 = (fun i j => raw23184step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23184step1 raw23184step0; decide +kernel
      have hl : raw23184step1Labels = raw23184step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23184step0 raw23184step0Labels permutation39 permutation3
    _ = mixedMoment B node1333 node1333Labels := by rfl

def raw23185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw23185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23185 raw23185Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw23185 raw23185Labels = mixedMoment B raw23185step0 raw23185step0Labels := by
      have hz : ∀ j, raw23185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23185step0 = (fun i j => raw23185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23185step0 raw23185; decide +kernel
      have hl : raw23185step0Labels = raw23185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23185 raw23185Labels permutation346 hz
    mixedMoment B raw23185step0 raw23185step0Labels = mixedMoment B raw23185step1 raw23185step1Labels := by
      have ha : raw23185step1 = (fun i j => raw23185step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23185step1 raw23185step0; decide +kernel
      have hl : raw23185step1Labels = raw23185step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23185step0 raw23185step0Labels permutation39 permutation3
    _ = mixedMoment B node1333 node1333Labels := by rfl

def raw23186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw23186step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23186 raw23186Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw23186 raw23186Labels = mixedMoment B raw23186step0 raw23186step0Labels := by
      have hz : ∀ j, raw23186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23186step0 = (fun i j => raw23186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23186step0 raw23186; decide +kernel
      have hl : raw23186step0Labels = raw23186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23186 raw23186Labels permutation434 hz
    mixedMoment B raw23186step0 raw23186step0Labels = mixedMoment B raw23186step1 raw23186step1Labels := by
      have hz : ∀ j, raw23186step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23186step1 = (fun i j => raw23186step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23186step1 raw23186step0; decide +kernel
      have hl : raw23186step1Labels = raw23186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23186step0 raw23186step0Labels permutation80 hz
    mixedMoment B raw23186step1 raw23186step1Labels = mixedMoment B raw23186step2 raw23186step2Labels := by
      have ha : raw23186step2 = (fun i j => raw23186step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23186step2 raw23186step1; decide +kernel
      have hl : raw23186step2Labels = raw23186step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23186step1 raw23186step1Labels permutation9 permutation3
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw23187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw23187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw23187step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23187step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23187 raw23187Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw23187 raw23187Labels = mixedMoment B raw23187step0 raw23187step0Labels := by
      have hz : ∀ j, raw23187 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23187step0 = (fun i j => raw23187 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23187step0 raw23187; decide +kernel
      have hl : raw23187step0Labels = raw23187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23187 raw23187Labels permutation434 hz
    mixedMoment B raw23187step0 raw23187step0Labels = mixedMoment B raw23187step1 raw23187step1Labels := by
      have hz : ∀ j, raw23187step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23187step1 = (fun i j => raw23187step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23187step1 raw23187step0; decide +kernel
      have hl : raw23187step1Labels = raw23187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23187step0 raw23187step0Labels permutation80 hz
    mixedMoment B raw23187step1 raw23187step1Labels = mixedMoment B raw23187step2 raw23187step2Labels := by
      have ha : raw23187step2 = (fun i j => raw23187step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23187step2 raw23187step1; decide +kernel
      have hl : raw23187step2Labels = raw23187step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23187step1 raw23187step1Labels permutation8 permutation3
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw23188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23188step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23188step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23188step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23188step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23188step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23188step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23188 raw23188Labels = mixedMoment B node1536 node1536Labels := by
  calc
    mixedMoment B raw23188 raw23188Labels = mixedMoment B raw23188step0 raw23188step0Labels := by
      have hz : ∀ j, raw23188 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23188step0 = (fun i j => raw23188 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23188step0 raw23188; decide +kernel
      have hl : raw23188step0Labels = raw23188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23188 raw23188Labels permutation434 hz
    mixedMoment B raw23188step0 raw23188step0Labels = mixedMoment B raw23188step1 raw23188step1Labels := by
      have hz : ∀ j, raw23188step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23188step1 = (fun i j => raw23188step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23188step1 raw23188step0; decide +kernel
      have hl : raw23188step1Labels = raw23188step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23188step0 raw23188step0Labels permutation80 hz
    mixedMoment B raw23188step1 raw23188step1Labels = mixedMoment B raw23188step2 raw23188step2Labels := by
      have ha : raw23188step2 = (fun i j => raw23188step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23188step2 raw23188step1; decide +kernel
      have hl : raw23188step2Labels = raw23188step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23188step1 raw23188step1Labels permutation8 permutation7
    mixedMoment B raw23188step2 raw23188step2Labels = mixedMoment B raw23188step3 raw23188step3Labels := by
      have ha : raw23188step3 = -raw23188step2 := by apply Matrix.ext; change ∀ i j, raw23188step3 i j = -(raw23188step2 i j); unfold raw23188step3 raw23188step2; decide +kernel
      have hl : raw23188step3Labels = raw23188step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23188step3 raw23188step3Labels = mixedMoment B raw23188step4 raw23188step4Labels := by
      have ha : raw23188step4 = raw23188step3 := by apply Matrix.ext; unfold raw23188step4 raw23188step3; decide +kernel
      have hl : raw23188step3Labels = labelEmbedding1 ∘ raw23188step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23188step3 raw23188step3Labels raw23188step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1536 node1536Labels := by rfl

def raw23189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23189 raw23189Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw23189 raw23189Labels = mixedMoment B raw23189step0 raw23189step0Labels := by
      have hz : ∀ j, raw23189 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23189step0 = (fun i j => raw23189 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23189step0 raw23189; decide +kernel
      have hl : raw23189step0Labels = raw23189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23189 raw23189Labels permutation434 hz
    mixedMoment B raw23189step0 raw23189step0Labels = mixedMoment B raw23189step1 raw23189step1Labels := by
      have ha : raw23189step1 = (fun i j => raw23189step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23189step1 raw23189step0; decide +kernel
      have hl : raw23189step1Labels = raw23189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23189step0 raw23189step0Labels permutation38 permutation7
    mixedMoment B raw23189step1 raw23189step1Labels = mixedMoment B raw23189step2 raw23189step2Labels := by
      have ha : raw23189step2 = -raw23189step1 := by apply Matrix.ext; change ∀ i j, raw23189step2 i j = -(raw23189step1 i j); unfold raw23189step2 raw23189step1; decide +kernel
      have hl : raw23189step2Labels = raw23189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23189step2 raw23189step2Labels = mixedMoment B raw23189step3 raw23189step3Labels := by
      have ha : raw23189step3 = raw23189step2 := by apply Matrix.ext; unfold raw23189step3 raw23189step2; decide +kernel
      have hl : raw23189step2Labels = labelEmbedding1 ∘ raw23189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23189step2 raw23189step2Labels raw23189step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

def raw23190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23190 raw23190Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw23190 raw23190Labels = mixedMoment B raw23190step0 raw23190step0Labels := by
      have hz : ∀ j, raw23190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23190step0 = (fun i j => raw23190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23190step0 raw23190; decide +kernel
      have hl : raw23190step0Labels = raw23190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23190 raw23190Labels permutation346 hz
    mixedMoment B raw23190step0 raw23190step0Labels = mixedMoment B raw23190step1 raw23190step1Labels := by
      have ha : raw23190step1 = (fun i j => raw23190step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23190step1 raw23190step0; decide +kernel
      have hl : raw23190step1Labels = raw23190step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23190step0 raw23190step0Labels permutation38 permutation7
    mixedMoment B raw23190step1 raw23190step1Labels = mixedMoment B raw23190step2 raw23190step2Labels := by
      have ha : raw23190step2 = -raw23190step1 := by apply Matrix.ext; change ∀ i j, raw23190step2 i j = -(raw23190step1 i j); unfold raw23190step2 raw23190step1; decide +kernel
      have hl : raw23190step2Labels = raw23190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23190step2 raw23190step2Labels = mixedMoment B raw23190step3 raw23190step3Labels := by
      have ha : raw23190step3 = raw23190step2 := by apply Matrix.ext; unfold raw23190step3 raw23190step2; decide +kernel
      have hl : raw23190step2Labels = labelEmbedding1 ∘ raw23190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23190step2 raw23190step2Labels raw23190step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

def raw23191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23191step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23191step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23191step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23191step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23191step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23191step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23191 raw23191Labels = mixedMoment B node1753 node1753Labels := by
  calc
    mixedMoment B raw23191 raw23191Labels = mixedMoment B raw23191step0 raw23191step0Labels := by
      have hz : ∀ j, raw23191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23191step0 = (fun i j => raw23191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23191step0 raw23191; decide +kernel
      have hl : raw23191step0Labels = raw23191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23191 raw23191Labels permutation434 hz
    mixedMoment B raw23191step0 raw23191step0Labels = mixedMoment B raw23191step1 raw23191step1Labels := by
      have hz : ∀ j, raw23191step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23191step1 = (fun i j => raw23191step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23191step1 raw23191step0; decide +kernel
      have hl : raw23191step1Labels = raw23191step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23191step0 raw23191step0Labels permutation80 hz
    mixedMoment B raw23191step1 raw23191step1Labels = mixedMoment B raw23191step2 raw23191step2Labels := by
      have ha : raw23191step2 = (fun i j => raw23191step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23191step2 raw23191step1; decide +kernel
      have hl : raw23191step2Labels = raw23191step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23191step1 raw23191step1Labels permutation9 permutation7
    mixedMoment B raw23191step2 raw23191step2Labels = mixedMoment B raw23191step3 raw23191step3Labels := by
      have ha : raw23191step3 = -raw23191step2 := by apply Matrix.ext; change ∀ i j, raw23191step3 i j = -(raw23191step2 i j); unfold raw23191step3 raw23191step2; decide +kernel
      have hl : raw23191step3Labels = raw23191step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23191step3 raw23191step3Labels = mixedMoment B raw23191step4 raw23191step4Labels := by
      have ha : raw23191step4 = raw23191step3 := by apply Matrix.ext; unfold raw23191step4 raw23191step3; decide +kernel
      have hl : raw23191step3Labels = labelEmbedding1 ∘ raw23191step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23191step3 raw23191step3Labels raw23191step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1753 node1753Labels := by rfl

def raw23192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23192step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23192step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23192step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23192 raw23192Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw23192 raw23192Labels = mixedMoment B raw23192step0 raw23192step0Labels := by
      have hz : ∀ j, raw23192 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23192step0 = (fun i j => raw23192 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23192step0 raw23192; decide +kernel
      have hl : raw23192step0Labels = raw23192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23192 raw23192Labels permutation434 hz
    mixedMoment B raw23192step0 raw23192step0Labels = mixedMoment B raw23192step1 raw23192step1Labels := by
      have ha : raw23192step1 = (fun i j => raw23192step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23192step1 raw23192step0; decide +kernel
      have hl : raw23192step1Labels = raw23192step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23192step0 raw23192step0Labels permutation38 permutation7
    mixedMoment B raw23192step1 raw23192step1Labels = mixedMoment B raw23192step2 raw23192step2Labels := by
      have ha : raw23192step2 = -raw23192step1 := by apply Matrix.ext; change ∀ i j, raw23192step2 i j = -(raw23192step1 i j); unfold raw23192step2 raw23192step1; decide +kernel
      have hl : raw23192step2Labels = raw23192step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23192step2 raw23192step2Labels = mixedMoment B raw23192step3 raw23192step3Labels := by
      have ha : raw23192step3 = raw23192step2 := by apply Matrix.ext; unfold raw23192step3 raw23192step2; decide +kernel
      have hl : raw23192step2Labels = labelEmbedding1 ∘ raw23192step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23192step2 raw23192step2Labels raw23192step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

def raw23193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23193 raw23193Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw23193 raw23193Labels = mixedMoment B raw23193step0 raw23193step0Labels := by
      have hz : ∀ j, raw23193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23193step0 = (fun i j => raw23193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23193step0 raw23193; decide +kernel
      have hl : raw23193step0Labels = raw23193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23193 raw23193Labels permutation434 hz
    mixedMoment B raw23193step0 raw23193step0Labels = mixedMoment B raw23193step1 raw23193step1Labels := by
      have ha : raw23193step1 = (fun i j => raw23193step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23193step1 raw23193step0; decide +kernel
      have hl : raw23193step1Labels = raw23193step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23193step0 raw23193step0Labels permutation38 permutation7
    mixedMoment B raw23193step1 raw23193step1Labels = mixedMoment B raw23193step2 raw23193step2Labels := by
      have ha : raw23193step2 = -raw23193step1 := by apply Matrix.ext; change ∀ i j, raw23193step2 i j = -(raw23193step1 i j); unfold raw23193step2 raw23193step1; decide +kernel
      have hl : raw23193step2Labels = raw23193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23193step2 raw23193step2Labels = mixedMoment B raw23193step3 raw23193step3Labels := by
      have ha : raw23193step3 = raw23193step2 := by apply Matrix.ext; unfold raw23193step3 raw23193step2; decide +kernel
      have hl : raw23193step2Labels = labelEmbedding1 ∘ raw23193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23193step2 raw23193step2Labels raw23193step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

def raw23194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23194 raw23194Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw23194 raw23194Labels = mixedMoment B raw23194step0 raw23194step0Labels := by
      have ha : raw23194step0 = (fun i j => raw23194 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23194step0 raw23194; decide +kernel
      have hl : raw23194step0Labels = raw23194Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23194 raw23194Labels permutation206 permutation7
    mixedMoment B raw23194step0 raw23194step0Labels = mixedMoment B raw23194step1 raw23194step1Labels := by
      have ha : raw23194step1 = -raw23194step0 := by apply Matrix.ext; change ∀ i j, raw23194step1 i j = -(raw23194step0 i j); unfold raw23194step1 raw23194step0; decide +kernel
      have hl : raw23194step1Labels = raw23194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23194step1 raw23194step1Labels = mixedMoment B raw23194step2 raw23194step2Labels := by
      have ha : raw23194step2 = raw23194step1 := by apply Matrix.ext; unfold raw23194step2 raw23194step1; decide +kernel
      have hl : raw23194step1Labels = labelEmbedding1 ∘ raw23194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23194step1 raw23194step1Labels raw23194step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1671 node1671Labels := by rfl

def raw23195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23195 raw23195Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23195 raw23195Labels = mixedMoment B raw23195step0 raw23195step0Labels := by
      have hz : ∀ j, raw23195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23195step0 = (fun i j => raw23195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23195step0 raw23195; decide +kernel
      have hl : raw23195step0Labels = raw23195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23195 raw23195Labels permutation434 hz
    mixedMoment B raw23195step0 raw23195step0Labels = mixedMoment B raw23195step1 raw23195step1Labels := by
      have ha : raw23195step1 = (fun i j => raw23195step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23195step1 raw23195step0; decide +kernel
      have hl : raw23195step1Labels = raw23195step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23195step0 raw23195step0Labels permutation39 permutation7
    mixedMoment B raw23195step1 raw23195step1Labels = mixedMoment B raw23195step2 raw23195step2Labels := by
      have ha : raw23195step2 = -raw23195step1 := by apply Matrix.ext; change ∀ i j, raw23195step2 i j = -(raw23195step1 i j); unfold raw23195step2 raw23195step1; decide +kernel
      have hl : raw23195step2Labels = raw23195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23195step2 raw23195step2Labels = mixedMoment B raw23195step3 raw23195step3Labels := by
      have ha : raw23195step3 = raw23195step2 := by apply Matrix.ext; unfold raw23195step3 raw23195step2; decide +kernel
      have hl : raw23195step2Labels = labelEmbedding1 ∘ raw23195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23195step2 raw23195step2Labels raw23195step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw23196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23196step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23196step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23196step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23196 raw23196Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw23196 raw23196Labels = mixedMoment B raw23196step0 raw23196step0Labels := by
      have hz : ∀ j, raw23196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23196step0 = (fun i j => raw23196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23196step0 raw23196; decide +kernel
      have hl : raw23196step0Labels = raw23196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23196 raw23196Labels permutation346 hz
    mixedMoment B raw23196step0 raw23196step0Labels = mixedMoment B raw23196step1 raw23196step1Labels := by
      have ha : raw23196step1 = (fun i j => raw23196step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23196step1 raw23196step0; decide +kernel
      have hl : raw23196step1Labels = raw23196step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23196step0 raw23196step0Labels permutation38 permutation7
    mixedMoment B raw23196step1 raw23196step1Labels = mixedMoment B raw23196step2 raw23196step2Labels := by
      have ha : raw23196step2 = -raw23196step1 := by apply Matrix.ext; change ∀ i j, raw23196step2 i j = -(raw23196step1 i j); unfold raw23196step2 raw23196step1; decide +kernel
      have hl : raw23196step2Labels = raw23196step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23196step2 raw23196step2Labels = mixedMoment B raw23196step3 raw23196step3Labels := by
      have ha : raw23196step3 = raw23196step2 := by apply Matrix.ext; unfold raw23196step3 raw23196step2; decide +kernel
      have hl : raw23196step2Labels = labelEmbedding1 ∘ raw23196step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23196step2 raw23196step2Labels raw23196step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

def raw23197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23197step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23197 raw23197Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw23197 raw23197Labels = mixedMoment B raw23197step0 raw23197step0Labels := by
      have hz : ∀ j, raw23197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23197step0 = (fun i j => raw23197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23197step0 raw23197; decide +kernel
      have hl : raw23197step0Labels = raw23197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23197 raw23197Labels permutation346 hz
    mixedMoment B raw23197step0 raw23197step0Labels = mixedMoment B raw23197step1 raw23197step1Labels := by
      have ha : raw23197step1 = (fun i j => raw23197step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23197step1 raw23197step0; decide +kernel
      have hl : raw23197step1Labels = raw23197step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23197step0 raw23197step0Labels permutation38 permutation7
    mixedMoment B raw23197step1 raw23197step1Labels = mixedMoment B raw23197step2 raw23197step2Labels := by
      have ha : raw23197step2 = -raw23197step1 := by apply Matrix.ext; change ∀ i j, raw23197step2 i j = -(raw23197step1 i j); unfold raw23197step2 raw23197step1; decide +kernel
      have hl : raw23197step2Labels = raw23197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23197step2 raw23197step2Labels = mixedMoment B raw23197step3 raw23197step3Labels := by
      have ha : raw23197step3 = raw23197step2 := by apply Matrix.ext; unfold raw23197step3 raw23197step2; decide +kernel
      have hl : raw23197step2Labels = labelEmbedding1 ∘ raw23197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23197step2 raw23197step2Labels raw23197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

def raw23198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23198step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23198 raw23198Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw23198 raw23198Labels = mixedMoment B raw23198step0 raw23198step0Labels := by
      have ha : raw23198step0 = (fun i j => raw23198 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23198step0 raw23198; decide +kernel
      have hl : raw23198step0Labels = raw23198Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23198 raw23198Labels permutation182 permutation7
    mixedMoment B raw23198step0 raw23198step0Labels = mixedMoment B raw23198step1 raw23198step1Labels := by
      have ha : raw23198step1 = -raw23198step0 := by apply Matrix.ext; change ∀ i j, raw23198step1 i j = -(raw23198step0 i j); unfold raw23198step1 raw23198step0; decide +kernel
      have hl : raw23198step1Labels = raw23198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23198step1 raw23198step1Labels = mixedMoment B raw23198step2 raw23198step2Labels := by
      have ha : raw23198step2 = raw23198step1 := by apply Matrix.ext; unfold raw23198step2 raw23198step1; decide +kernel
      have hl : raw23198step1Labels = labelEmbedding1 ∘ raw23198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23198step1 raw23198step1Labels raw23198step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1671 node1671Labels := by rfl

def raw23199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23199step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23199step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23199step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23199 raw23199Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23199 raw23199Labels = mixedMoment B raw23199step0 raw23199step0Labels := by
      have hz : ∀ j, raw23199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23199step0 = (fun i j => raw23199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23199step0 raw23199; decide +kernel
      have hl : raw23199step0Labels = raw23199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23199 raw23199Labels permutation346 hz
    mixedMoment B raw23199step0 raw23199step0Labels = mixedMoment B raw23199step1 raw23199step1Labels := by
      have ha : raw23199step1 = (fun i j => raw23199step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23199step1 raw23199step0; decide +kernel
      have hl : raw23199step1Labels = raw23199step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23199step0 raw23199step0Labels permutation39 permutation7
    mixedMoment B raw23199step1 raw23199step1Labels = mixedMoment B raw23199step2 raw23199step2Labels := by
      have ha : raw23199step2 = -raw23199step1 := by apply Matrix.ext; change ∀ i j, raw23199step2 i j = -(raw23199step1 i j); unfold raw23199step2 raw23199step1; decide +kernel
      have hl : raw23199step2Labels = raw23199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23199step2 raw23199step2Labels = mixedMoment B raw23199step3 raw23199step3Labels := by
      have ha : raw23199step3 = raw23199step2 := by apply Matrix.ext; unfold raw23199step3 raw23199step2; decide +kernel
      have hl : raw23199step2Labels = labelEmbedding1 ∘ raw23199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23199step2 raw23199step2Labels raw23199step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw23200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23200step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw23200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23200step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23200step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23200 raw23200Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw23200 raw23200Labels = mixedMoment B raw23200step0 raw23200step0Labels := by
      have hz : ∀ j, raw23200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23200step0 = (fun i j => raw23200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23200step0 raw23200; decide +kernel
      have hl : raw23200step0Labels = raw23200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23200 raw23200Labels permutation434 hz
    mixedMoment B raw23200step0 raw23200step0Labels = mixedMoment B raw23200step1 raw23200step1Labels := by
      have hz : ∀ j, raw23200step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23200step1 = (fun i j => raw23200step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23200step1 raw23200step0; decide +kernel
      have hl : raw23200step1Labels = raw23200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23200step0 raw23200step0Labels permutation80 hz
    mixedMoment B raw23200step1 raw23200step1Labels = mixedMoment B raw23200step2 raw23200step2Labels := by
      have ha : raw23200step2 = (fun i j => raw23200step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23200step2 raw23200step1; decide +kernel
      have hl : raw23200step2Labels = raw23200step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23200step1 raw23200step1Labels permutation9 permutation7
    mixedMoment B raw23200step2 raw23200step2Labels = mixedMoment B raw23200step3 raw23200step3Labels := by
      have ha : raw23200step3 = -raw23200step2 := by apply Matrix.ext; change ∀ i j, raw23200step3 i j = -(raw23200step2 i j); unfold raw23200step3 raw23200step2; decide +kernel
      have hl : raw23200step3Labels = raw23200step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23200step3 raw23200step3Labels = mixedMoment B raw23200step4 raw23200step4Labels := by
      have ha : raw23200step4 = raw23200step3 := by apply Matrix.ext; unfold raw23200step4 raw23200step3; decide +kernel
      have hl : raw23200step3Labels = labelEmbedding1 ∘ raw23200step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23200step3 raw23200step3Labels raw23200step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

def raw23201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23201step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw23201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw23201step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23201step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw23201step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23201 raw23201Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw23201 raw23201Labels = mixedMoment B raw23201step0 raw23201step0Labels := by
      have hz : ∀ j, raw23201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23201step0 = (fun i j => raw23201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23201step0 raw23201; decide +kernel
      have hl : raw23201step0Labels = raw23201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23201 raw23201Labels permutation434 hz
    mixedMoment B raw23201step0 raw23201step0Labels = mixedMoment B raw23201step1 raw23201step1Labels := by
      have hz : ∀ j, raw23201step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23201step1 = (fun i j => raw23201step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23201step1 raw23201step0; decide +kernel
      have hl : raw23201step1Labels = raw23201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23201step0 raw23201step0Labels permutation80 hz
    mixedMoment B raw23201step1 raw23201step1Labels = mixedMoment B raw23201step2 raw23201step2Labels := by
      have ha : raw23201step2 = (fun i j => raw23201step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23201step2 raw23201step1; decide +kernel
      have hl : raw23201step2Labels = raw23201step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23201step1 raw23201step1Labels permutation9 permutation7
    mixedMoment B raw23201step2 raw23201step2Labels = mixedMoment B raw23201step3 raw23201step3Labels := by
      have ha : raw23201step3 = -raw23201step2 := by apply Matrix.ext; change ∀ i j, raw23201step3 i j = -(raw23201step2 i j); unfold raw23201step3 raw23201step2; decide +kernel
      have hl : raw23201step3Labels = raw23201step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23201step3 raw23201step3Labels = mixedMoment B raw23201step4 raw23201step4Labels := by
      have ha : raw23201step4 = raw23201step3 := by apply Matrix.ext; unfold raw23201step4 raw23201step3; decide +kernel
      have hl : raw23201step3Labels = labelEmbedding1 ∘ raw23201step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23201step3 raw23201step3Labels raw23201step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

def raw23202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw23202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23202 raw23202Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw23202 raw23202Labels = mixedMoment B raw23202step0 raw23202step0Labels := by
      have hz : ∀ j, raw23202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23202step0 = (fun i j => raw23202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23202step0 raw23202; decide +kernel
      have hl : raw23202step0Labels = raw23202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23202 raw23202Labels permutation434 hz
    mixedMoment B raw23202step0 raw23202step0Labels = mixedMoment B raw23202step1 raw23202step1Labels := by
      have ha : raw23202step1 = (fun i j => raw23202step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23202step1 raw23202step0; decide +kernel
      have hl : raw23202step1Labels = raw23202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23202step0 raw23202step0Labels permutation39 permutation7
    mixedMoment B raw23202step1 raw23202step1Labels = mixedMoment B raw23202step2 raw23202step2Labels := by
      have ha : raw23202step2 = -raw23202step1 := by apply Matrix.ext; change ∀ i j, raw23202step2 i j = -(raw23202step1 i j); unfold raw23202step2 raw23202step1; decide +kernel
      have hl : raw23202step2Labels = raw23202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23202step2 raw23202step2Labels = mixedMoment B raw23202step3 raw23202step3Labels := by
      have ha : raw23202step3 = raw23202step2 := by apply Matrix.ext; unfold raw23202step3 raw23202step2; decide +kernel
      have hl : raw23202step2Labels = labelEmbedding1 ∘ raw23202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23202step2 raw23202step2Labels raw23202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw23203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw23203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23203step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23203 raw23203Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw23203 raw23203Labels = mixedMoment B raw23203step0 raw23203step0Labels := by
      have hz : ∀ j, raw23203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23203step0 = (fun i j => raw23203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23203step0 raw23203; decide +kernel
      have hl : raw23203step0Labels = raw23203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23203 raw23203Labels permutation346 hz
    mixedMoment B raw23203step0 raw23203step0Labels = mixedMoment B raw23203step1 raw23203step1Labels := by
      have ha : raw23203step1 = (fun i j => raw23203step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23203step1 raw23203step0; decide +kernel
      have hl : raw23203step1Labels = raw23203step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23203step0 raw23203step0Labels permutation39 permutation7
    mixedMoment B raw23203step1 raw23203step1Labels = mixedMoment B raw23203step2 raw23203step2Labels := by
      have ha : raw23203step2 = -raw23203step1 := by apply Matrix.ext; change ∀ i j, raw23203step2 i j = -(raw23203step1 i j); unfold raw23203step2 raw23203step1; decide +kernel
      have hl : raw23203step2Labels = raw23203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23203step2 raw23203step2Labels = mixedMoment B raw23203step3 raw23203step3Labels := by
      have ha : raw23203step3 = raw23203step2 := by apply Matrix.ext; unfold raw23203step3 raw23203step2; decide +kernel
      have hl : raw23203step2Labels = labelEmbedding1 ∘ raw23203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23203step2 raw23203step2Labels raw23203step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw23204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw23204step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23204step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw23204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23204step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw23204step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23204step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw23204step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23204 raw23204Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw23204 raw23204Labels = mixedMoment B raw23204step0 raw23204step0Labels := by
      have hz : ∀ j, raw23204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23204step0 = (fun i j => raw23204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23204step0 raw23204; decide +kernel
      have hl : raw23204step0Labels = raw23204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23204 raw23204Labels permutation434 hz
    mixedMoment B raw23204step0 raw23204step0Labels = mixedMoment B raw23204step1 raw23204step1Labels := by
      have hz : ∀ j, raw23204step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23204step1 = (fun i j => raw23204step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23204step1 raw23204step0; decide +kernel
      have hl : raw23204step1Labels = raw23204step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23204step0 raw23204step0Labels permutation80 hz
    mixedMoment B raw23204step1 raw23204step1Labels = mixedMoment B raw23204step2 raw23204step2Labels := by
      have ha : raw23204step2 = (fun i j => raw23204step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23204step2 raw23204step1; decide +kernel
      have hl : raw23204step2Labels = raw23204step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23204step1 raw23204step1Labels permutation9 permutation7
    mixedMoment B raw23204step2 raw23204step2Labels = mixedMoment B raw23204step3 raw23204step3Labels := by
      have ha : raw23204step3 = -raw23204step2 := by apply Matrix.ext; change ∀ i j, raw23204step3 i j = -(raw23204step2 i j); unfold raw23204step3 raw23204step2; decide +kernel
      have hl : raw23204step3Labels = raw23204step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23204step3 raw23204step3Labels = mixedMoment B raw23204step4 raw23204step4Labels := by
      have ha : raw23204step4 = raw23204step3 := by apply Matrix.ext; unfold raw23204step4 raw23204step3; decide +kernel
      have hl : raw23204step3Labels = labelEmbedding1 ∘ raw23204step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23204step3 raw23204step3Labels raw23204step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw23205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23205 raw23205Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw23205 raw23205Labels = mixedMoment B raw23205step0 raw23205step0Labels := by
      have hz : ∀ j, raw23205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23205step0 = (fun i j => raw23205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23205step0 raw23205; decide +kernel
      have hl : raw23205step0Labels = raw23205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23205 raw23205Labels permutation434 hz
    mixedMoment B raw23205step0 raw23205step0Labels = mixedMoment B raw23205step1 raw23205step1Labels := by
      have hz : ∀ j, raw23205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23205step1 = (fun i j => raw23205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23205step1 raw23205step0; decide +kernel
      have hl : raw23205step1Labels = raw23205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23205step0 raw23205step0Labels permutation80 hz
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw23206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23206 raw23206Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw23206 raw23206Labels = mixedMoment B raw23206step0 raw23206step0Labels := by
      have hz : ∀ j, raw23206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23206step0 = (fun i j => raw23206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23206step0 raw23206; decide +kernel
      have hl : raw23206step0Labels = raw23206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23206 raw23206Labels permutation434 hz
    mixedMoment B raw23206step0 raw23206step0Labels = mixedMoment B raw23206step1 raw23206step1Labels := by
      have hz : ∀ j, raw23206step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23206step1 = (fun i j => raw23206step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23206step1 raw23206step0; decide +kernel
      have hl : raw23206step1Labels = raw23206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23206step0 raw23206step0Labels permutation80 hz
    _ = mixedMoment B node614 node614Labels := by rfl

def raw23207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23207 raw23207Labels = mixedMoment B node583 node583Labels := by
  calc
    mixedMoment B raw23207 raw23207Labels = mixedMoment B raw23207step0 raw23207step0Labels := by
      have hz : ∀ j, raw23207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23207step0 = (fun i j => raw23207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23207step0 raw23207; decide +kernel
      have hl : raw23207step0Labels = raw23207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23207 raw23207Labels permutation434 hz
    _ = mixedMoment B node583 node583Labels := by rfl

def raw23208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23208 raw23208Labels = mixedMoment B node583 node583Labels := by
  calc
    mixedMoment B raw23208 raw23208Labels = mixedMoment B raw23208step0 raw23208step0Labels := by
      have hz : ∀ j, raw23208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23208step0 = (fun i j => raw23208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23208step0 raw23208; decide +kernel
      have hl : raw23208step0Labels = raw23208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23208 raw23208Labels permutation346 hz
    _ = mixedMoment B node583 node583Labels := by rfl

def raw23209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23209 raw23209Labels = mixedMoment B node589 node589Labels := by
  calc
    mixedMoment B raw23209 raw23209Labels = mixedMoment B raw23209step0 raw23209step0Labels := by
      have hz : ∀ j, raw23209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23209step0 = (fun i j => raw23209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23209step0 raw23209; decide +kernel
      have hl : raw23209step0Labels = raw23209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23209 raw23209Labels permutation434 hz
    mixedMoment B raw23209step0 raw23209step0Labels = mixedMoment B raw23209step1 raw23209step1Labels := by
      have hz : ∀ j, raw23209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23209step1 = (fun i j => raw23209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23209step1 raw23209step0; decide +kernel
      have hl : raw23209step1Labels = raw23209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23209step0 raw23209step0Labels permutation80 hz
    mixedMoment B raw23209step1 raw23209step1Labels = mixedMoment B raw23209step2 raw23209step2Labels := by
      have ha : raw23209step2 = (fun i j => raw23209step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23209step2 raw23209step1; decide +kernel
      have hl : raw23209step2Labels = raw23209step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23209step1 raw23209step1Labels permutation9 permutation2
    _ = mixedMoment B node589 node589Labels := by rfl

def raw23210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23210 raw23210Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw23210 raw23210Labels = mixedMoment B raw23210step0 raw23210step0Labels := by
      have hz : ∀ j, raw23210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23210step0 = (fun i j => raw23210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23210step0 raw23210; decide +kernel
      have hl : raw23210step0Labels = raw23210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23210 raw23210Labels permutation434 hz
    mixedMoment B raw23210step0 raw23210step0Labels = mixedMoment B raw23210step1 raw23210step1Labels := by
      have ha : raw23210step1 = (fun i j => raw23210step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23210step1 raw23210step0; decide +kernel
      have hl : raw23210step1Labels = raw23210step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23210step0 raw23210step0Labels permutation38 permutation2
    _ = mixedMoment B node933 node933Labels := by rfl

def raw23211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23211step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23211 raw23211Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw23211 raw23211Labels = mixedMoment B raw23211step0 raw23211step0Labels := by
      have hz : ∀ j, raw23211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23211step0 = (fun i j => raw23211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23211step0 raw23211; decide +kernel
      have hl : raw23211step0Labels = raw23211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23211 raw23211Labels permutation346 hz
    mixedMoment B raw23211step0 raw23211step0Labels = mixedMoment B raw23211step1 raw23211step1Labels := by
      have ha : raw23211step1 = (fun i j => raw23211step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23211step1 raw23211step0; decide +kernel
      have hl : raw23211step1Labels = raw23211step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23211step0 raw23211step0Labels permutation38 permutation2
    _ = mixedMoment B node933 node933Labels := by rfl

def raw23212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23212 raw23212Labels = mixedMoment B node1086 node1086Labels := by
  calc
    mixedMoment B raw23212 raw23212Labels = mixedMoment B raw23212step0 raw23212step0Labels := by
      have hz : ∀ j, raw23212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23212step0 = (fun i j => raw23212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23212step0 raw23212; decide +kernel
      have hl : raw23212step0Labels = raw23212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23212 raw23212Labels permutation434 hz
    mixedMoment B raw23212step0 raw23212step0Labels = mixedMoment B raw23212step1 raw23212step1Labels := by
      have hz : ∀ j, raw23212step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23212step1 = (fun i j => raw23212step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23212step1 raw23212step0; decide +kernel
      have hl : raw23212step1Labels = raw23212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23212step0 raw23212step0Labels permutation80 hz
    mixedMoment B raw23212step1 raw23212step1Labels = mixedMoment B raw23212step2 raw23212step2Labels := by
      have ha : raw23212step2 = (fun i j => raw23212step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23212step2 raw23212step1; decide +kernel
      have hl : raw23212step2Labels = raw23212step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23212step1 raw23212step1Labels permutation9 permutation2
    _ = mixedMoment B node1086 node1086Labels := by rfl

def raw23213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23213 raw23213Labels = mixedMoment B node947 node947Labels := by
  calc
    mixedMoment B raw23213 raw23213Labels = mixedMoment B raw23213step0 raw23213step0Labels := by
      have hz : ∀ j, raw23213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23213step0 = (fun i j => raw23213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23213step0 raw23213; decide +kernel
      have hl : raw23213step0Labels = raw23213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23213 raw23213Labels permutation434 hz
    _ = mixedMoment B node947 node947Labels := by rfl

def raw23214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23214 raw23214Labels = mixedMoment B node947 node947Labels := by
  calc
    mixedMoment B raw23214 raw23214Labels = mixedMoment B raw23214step0 raw23214step0Labels := by
      have hz : ∀ j, raw23214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23214step0 = (fun i j => raw23214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23214step0 raw23214; decide +kernel
      have hl : raw23214step0Labels = raw23214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23214 raw23214Labels permutation346 hz
    _ = mixedMoment B node947 node947Labels := by rfl

def raw23215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23215 raw23215Labels = mixedMoment B node953 node953Labels := by
  calc
    mixedMoment B raw23215 raw23215Labels = mixedMoment B raw23215step0 raw23215step0Labels := by
      have hz : ∀ j, raw23215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23215step0 = (fun i j => raw23215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23215step0 raw23215; decide +kernel
      have hl : raw23215step0Labels = raw23215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23215 raw23215Labels permutation434 hz
    mixedMoment B raw23215step0 raw23215step0Labels = mixedMoment B raw23215step1 raw23215step1Labels := by
      have hz : ∀ j, raw23215step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23215step1 = (fun i j => raw23215step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23215step1 raw23215step0; decide +kernel
      have hl : raw23215step1Labels = raw23215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23215step0 raw23215step0Labels permutation80 hz
    mixedMoment B raw23215step1 raw23215step1Labels = mixedMoment B raw23215step2 raw23215step2Labels := by
      have ha : raw23215step2 = (fun i j => raw23215step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23215step2 raw23215step1; decide +kernel
      have hl : raw23215step2Labels = raw23215step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23215step1 raw23215step1Labels permutation9 permutation2
    _ = mixedMoment B node953 node953Labels := by rfl

def raw23216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23216 raw23216Labels = mixedMoment B node907 node907Labels := by
  calc
    mixedMoment B raw23216 raw23216Labels = mixedMoment B raw23216step0 raw23216step0Labels := by
      have ha : raw23216step0 = (fun i j => raw23216 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23216step0 raw23216; decide +kernel
      have hl : raw23216step0Labels = raw23216Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23216 raw23216Labels permutation200 permutation2
    _ = mixedMoment B node907 node907Labels := by rfl

def raw23217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23217 raw23217Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw23217 raw23217Labels = mixedMoment B raw23217step0 raw23217step0Labels := by
      have hz : ∀ j, raw23217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23217step0 = (fun i j => raw23217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23217step0 raw23217; decide +kernel
      have hl : raw23217step0Labels = raw23217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23217 raw23217Labels permutation434 hz
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw23218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23218 raw23218Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw23218 raw23218Labels = mixedMoment B raw23218step0 raw23218step0Labels := by
      have hz : ∀ j, raw23218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23218step0 = (fun i j => raw23218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23218step0 raw23218; decide +kernel
      have hl : raw23218step0Labels = raw23218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23218 raw23218Labels permutation434 hz
    mixedMoment B raw23218step0 raw23218step0Labels = mixedMoment B raw23218step1 raw23218step1Labels := by
      have ha : raw23218step1 = (fun i j => raw23218step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23218step1 raw23218step0; decide +kernel
      have hl : raw23218step1Labels = raw23218step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23218step0 raw23218step0Labels permutation33 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw23219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23219step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23219 raw23219Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw23219 raw23219Labels = mixedMoment B raw23219step0 raw23219step0Labels := by
      have hz : ∀ j, raw23219 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23219step0 = (fun i j => raw23219 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23219step0 raw23219; decide +kernel
      have hl : raw23219step0Labels = raw23219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23219 raw23219Labels permutation434 hz
    mixedMoment B raw23219step0 raw23219step0Labels = mixedMoment B raw23219step1 raw23219step1Labels := by
      have ha : raw23219step1 = (fun i j => raw23219step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23219step1 raw23219step0; decide +kernel
      have hl : raw23219step1Labels = raw23219step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23219step0 raw23219step0Labels permutation38 permutation3
    mixedMoment B raw23219step1 raw23219step1Labels = mixedMoment B raw23219step2 raw23219step2Labels := by
      have ha : raw23219step2 = raw23219step1 := by apply Matrix.ext; unfold raw23219step2 raw23219step1; decide +kernel
      have hl : raw23219step1Labels = labelEmbedding6 ∘ raw23219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23219step1 raw23219step1Labels raw23219step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw23220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23220step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23220step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23220 raw23220Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw23220 raw23220Labels = mixedMoment B raw23220step0 raw23220step0Labels := by
      have hz : ∀ j, raw23220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23220step0 = (fun i j => raw23220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23220step0 raw23220; decide +kernel
      have hl : raw23220step0Labels = raw23220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23220 raw23220Labels permutation346 hz
    mixedMoment B raw23220step0 raw23220step0Labels = mixedMoment B raw23220step1 raw23220step1Labels := by
      have ha : raw23220step1 = (fun i j => raw23220step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23220step1 raw23220step0; decide +kernel
      have hl : raw23220step1Labels = raw23220step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23220step0 raw23220step0Labels permutation38 permutation3
    mixedMoment B raw23220step1 raw23220step1Labels = mixedMoment B raw23220step2 raw23220step2Labels := by
      have ha : raw23220step2 = raw23220step1 := by apply Matrix.ext; unfold raw23220step2 raw23220step1; decide +kernel
      have hl : raw23220step1Labels = labelEmbedding6 ∘ raw23220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23220step1 raw23220step1Labels raw23220step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw23221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw23221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23221step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23221step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23221 raw23221Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw23221 raw23221Labels = mixedMoment B raw23221step0 raw23221step0Labels := by
      have hz : ∀ j, raw23221 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23221step0 = (fun i j => raw23221 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23221step0 raw23221; decide +kernel
      have hl : raw23221step0Labels = raw23221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23221 raw23221Labels permutation434 hz
    mixedMoment B raw23221step0 raw23221step0Labels = mixedMoment B raw23221step1 raw23221step1Labels := by
      have hz : ∀ j, raw23221step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23221step1 = (fun i j => raw23221step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23221step1 raw23221step0; decide +kernel
      have hl : raw23221step1Labels = raw23221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23221step0 raw23221step0Labels permutation80 hz
    mixedMoment B raw23221step1 raw23221step1Labels = mixedMoment B raw23221step2 raw23221step2Labels := by
      have ha : raw23221step2 = (fun i j => raw23221step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23221step2 raw23221step1; decide +kernel
      have hl : raw23221step2Labels = raw23221step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23221step1 raw23221step1Labels permutation9 permutation3
    mixedMoment B raw23221step2 raw23221step2Labels = mixedMoment B raw23221step3 raw23221step3Labels := by
      have ha : raw23221step3 = raw23221step2 := by apply Matrix.ext; unfold raw23221step3 raw23221step2; decide +kernel
      have hl : raw23221step2Labels = labelEmbedding6 ∘ raw23221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23221step2 raw23221step2Labels raw23221step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw23222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23222step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23222step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23222 raw23222Labels = mixedMoment B node4133 node4133Labels := by
  calc
    mixedMoment B raw23222 raw23222Labels = mixedMoment B raw23222step0 raw23222step0Labels := by
      have hz : ∀ j, raw23222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23222step0 = (fun i j => raw23222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23222step0 raw23222; decide +kernel
      have hl : raw23222step0Labels = raw23222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23222 raw23222Labels permutation434 hz
    mixedMoment B raw23222step0 raw23222step0Labels = mixedMoment B raw23222step1 raw23222step1Labels := by
      have hz : ∀ j, raw23222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23222step1 = (fun i j => raw23222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23222step1 raw23222step0; decide +kernel
      have hl : raw23222step1Labels = raw23222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23222step0 raw23222step0Labels permutation80 hz
    mixedMoment B raw23222step1 raw23222step1Labels = mixedMoment B raw23222step2 raw23222step2Labels := by
      have ha : raw23222step2 = (fun i j => raw23222step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23222step2 raw23222step1; decide +kernel
      have hl : raw23222step2Labels = raw23222step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23222step1 raw23222step1Labels permutation8 permutation3
    mixedMoment B raw23222step2 raw23222step2Labels = mixedMoment B raw23222step3 raw23222step3Labels := by
      have ha : raw23222step3 = raw23222step2 := by apply Matrix.ext; unfold raw23222step3 raw23222step2; decide +kernel
      have hl : raw23222step2Labels = labelEmbedding6 ∘ raw23222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23222step2 raw23222step2Labels raw23222step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4133 node4133Labels := by rfl

def raw23223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23223step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23223 raw23223Labels = mixedMoment B node4314 node4314Labels := by
  calc
    mixedMoment B raw23223 raw23223Labels = mixedMoment B raw23223step0 raw23223step0Labels := by
      have hz : ∀ j, raw23223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23223step0 = (fun i j => raw23223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23223step0 raw23223; decide +kernel
      have hl : raw23223step0Labels = raw23223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23223 raw23223Labels permutation434 hz
    mixedMoment B raw23223step0 raw23223step0Labels = mixedMoment B raw23223step1 raw23223step1Labels := by
      have ha : raw23223step1 = (fun i j => raw23223step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23223step1 raw23223step0; decide +kernel
      have hl : raw23223step1Labels = raw23223step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23223step0 raw23223step0Labels permutation38 permutation3
    mixedMoment B raw23223step1 raw23223step1Labels = mixedMoment B raw23223step2 raw23223step2Labels := by
      have ha : raw23223step2 = raw23223step1 := by apply Matrix.ext; unfold raw23223step2 raw23223step1; decide +kernel
      have hl : raw23223step1Labels = labelEmbedding6 ∘ raw23223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23223step1 raw23223step1Labels raw23223step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4314 node4314Labels := by rfl

def raw23224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23224step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23224 raw23224Labels = mixedMoment B node4314 node4314Labels := by
  calc
    mixedMoment B raw23224 raw23224Labels = mixedMoment B raw23224step0 raw23224step0Labels := by
      have hz : ∀ j, raw23224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23224step0 = (fun i j => raw23224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23224step0 raw23224; decide +kernel
      have hl : raw23224step0Labels = raw23224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23224 raw23224Labels permutation346 hz
    mixedMoment B raw23224step0 raw23224step0Labels = mixedMoment B raw23224step1 raw23224step1Labels := by
      have ha : raw23224step1 = (fun i j => raw23224step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23224step1 raw23224step0; decide +kernel
      have hl : raw23224step1Labels = raw23224step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23224step0 raw23224step0Labels permutation38 permutation3
    mixedMoment B raw23224step1 raw23224step1Labels = mixedMoment B raw23224step2 raw23224step2Labels := by
      have ha : raw23224step2 = raw23224step1 := by apply Matrix.ext; unfold raw23224step2 raw23224step1; decide +kernel
      have hl : raw23224step1Labels = labelEmbedding6 ∘ raw23224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23224step1 raw23224step1Labels raw23224step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4314 node4314Labels := by rfl

def raw23225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw23225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23225step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23225 raw23225Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw23225 raw23225Labels = mixedMoment B raw23225step0 raw23225step0Labels := by
      have hz : ∀ j, raw23225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23225step0 = (fun i j => raw23225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23225step0 raw23225; decide +kernel
      have hl : raw23225step0Labels = raw23225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23225 raw23225Labels permutation434 hz
    mixedMoment B raw23225step0 raw23225step0Labels = mixedMoment B raw23225step1 raw23225step1Labels := by
      have hz : ∀ j, raw23225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23225step1 = (fun i j => raw23225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23225step1 raw23225step0; decide +kernel
      have hl : raw23225step1Labels = raw23225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23225step0 raw23225step0Labels permutation80 hz
    mixedMoment B raw23225step1 raw23225step1Labels = mixedMoment B raw23225step2 raw23225step2Labels := by
      have ha : raw23225step2 = (fun i j => raw23225step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23225step2 raw23225step1; decide +kernel
      have hl : raw23225step2Labels = raw23225step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23225step1 raw23225step1Labels permutation12 permutation3
    mixedMoment B raw23225step2 raw23225step2Labels = mixedMoment B raw23225step3 raw23225step3Labels := by
      have ha : raw23225step3 = raw23225step2 := by apply Matrix.ext; unfold raw23225step3 raw23225step2; decide +kernel
      have hl : raw23225step2Labels = labelEmbedding6 ∘ raw23225step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23225step2 raw23225step2Labels raw23225step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw23226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23226step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23226step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23226 raw23226Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw23226 raw23226Labels = mixedMoment B raw23226step0 raw23226step0Labels := by
      have hz : ∀ j, raw23226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23226step0 = (fun i j => raw23226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23226step0 raw23226; decide +kernel
      have hl : raw23226step0Labels = raw23226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23226 raw23226Labels permutation434 hz
    mixedMoment B raw23226step0 raw23226step0Labels = mixedMoment B raw23226step1 raw23226step1Labels := by
      have ha : raw23226step1 = (fun i j => raw23226step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23226step1 raw23226step0; decide +kernel
      have hl : raw23226step1Labels = raw23226step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23226step0 raw23226step0Labels permutation32 permutation3
    mixedMoment B raw23226step1 raw23226step1Labels = mixedMoment B raw23226step2 raw23226step2Labels := by
      have ha : raw23226step2 = raw23226step1 := by apply Matrix.ext; unfold raw23226step2 raw23226step1; decide +kernel
      have hl : raw23226step1Labels = labelEmbedding6 ∘ raw23226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23226step1 raw23226step1Labels raw23226step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4107 node4107Labels := by rfl

def raw23227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23227step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23227 raw23227Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw23227 raw23227Labels = mixedMoment B raw23227step0 raw23227step0Labels := by
      have hz : ∀ j, raw23227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23227step0 = (fun i j => raw23227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23227step0 raw23227; decide +kernel
      have hl : raw23227step0Labels = raw23227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23227 raw23227Labels permutation434 hz
    mixedMoment B raw23227step0 raw23227step0Labels = mixedMoment B raw23227step1 raw23227step1Labels := by
      have ha : raw23227step1 = (fun i j => raw23227step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23227step1 raw23227step0; decide +kernel
      have hl : raw23227step1Labels = raw23227step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23227step0 raw23227step0Labels permutation32 permutation3
    mixedMoment B raw23227step1 raw23227step1Labels = mixedMoment B raw23227step2 raw23227step2Labels := by
      have ha : raw23227step2 = raw23227step1 := by apply Matrix.ext; unfold raw23227step2 raw23227step1; decide +kernel
      have hl : raw23227step1Labels = labelEmbedding6 ∘ raw23227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23227step1 raw23227step1Labels raw23227step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw23228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23228step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23228 raw23228Labels = mixedMoment B node4292 node4292Labels := by
  calc
    mixedMoment B raw23228 raw23228Labels = mixedMoment B raw23228step0 raw23228step0Labels := by
      have ha : raw23228step0 = (fun i j => raw23228 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23228step0 raw23228; decide +kernel
      have hl : raw23228step0Labels = raw23228Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23228 raw23228Labels permutation200 permutation3
    mixedMoment B raw23228step0 raw23228step0Labels = mixedMoment B raw23228step1 raw23228step1Labels := by
      have ha : raw23228step1 = raw23228step0 := by apply Matrix.ext; unfold raw23228step1 raw23228step0; decide +kernel
      have hl : raw23228step0Labels = labelEmbedding6 ∘ raw23228step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23228step0 raw23228step0Labels raw23228step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4292 node4292Labels := by rfl

def raw23229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23229step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23229 raw23229Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23229 raw23229Labels = mixedMoment B raw23229step0 raw23229step0Labels := by
      have hz : ∀ j, raw23229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23229step0 = (fun i j => raw23229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23229step0 raw23229; decide +kernel
      have hl : raw23229step0Labels = raw23229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23229 raw23229Labels permutation434 hz
    mixedMoment B raw23229step0 raw23229step0Labels = mixedMoment B raw23229step1 raw23229step1Labels := by
      have ha : raw23229step1 = (fun i j => raw23229step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23229step1 raw23229step0; decide +kernel
      have hl : raw23229step1Labels = raw23229step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23229step0 raw23229step0Labels permutation36 permutation3
    mixedMoment B raw23229step1 raw23229step1Labels = mixedMoment B raw23229step2 raw23229step2Labels := by
      have ha : raw23229step2 = raw23229step1 := by apply Matrix.ext; unfold raw23229step2 raw23229step1; decide +kernel
      have hl : raw23229step1Labels = labelEmbedding6 ∘ raw23229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23229step1 raw23229step1Labels raw23229step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw23230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23230step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23230 raw23230Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw23230 raw23230Labels = mixedMoment B raw23230step0 raw23230step0Labels := by
      have hz : ∀ j, raw23230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23230step0 = (fun i j => raw23230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23230step0 raw23230; decide +kernel
      have hl : raw23230step0Labels = raw23230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23230 raw23230Labels permutation346 hz
    mixedMoment B raw23230step0 raw23230step0Labels = mixedMoment B raw23230step1 raw23230step1Labels := by
      have ha : raw23230step1 = (fun i j => raw23230step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23230step1 raw23230step0; decide +kernel
      have hl : raw23230step1Labels = raw23230step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23230step0 raw23230step0Labels permutation32 permutation3
    mixedMoment B raw23230step1 raw23230step1Labels = mixedMoment B raw23230step2 raw23230step2Labels := by
      have ha : raw23230step2 = raw23230step1 := by apply Matrix.ext; unfold raw23230step2 raw23230step1; decide +kernel
      have hl : raw23230step1Labels = labelEmbedding6 ∘ raw23230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23230step1 raw23230step1Labels raw23230step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4107 node4107Labels := by rfl

def raw23231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23231step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23231 raw23231Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw23231 raw23231Labels = mixedMoment B raw23231step0 raw23231step0Labels := by
      have hz : ∀ j, raw23231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23231step0 = (fun i j => raw23231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23231step0 raw23231; decide +kernel
      have hl : raw23231step0Labels = raw23231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23231 raw23231Labels permutation346 hz
    mixedMoment B raw23231step0 raw23231step0Labels = mixedMoment B raw23231step1 raw23231step1Labels := by
      have ha : raw23231step1 = (fun i j => raw23231step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23231step1 raw23231step0; decide +kernel
      have hl : raw23231step1Labels = raw23231step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23231step0 raw23231step0Labels permutation32 permutation3
    mixedMoment B raw23231step1 raw23231step1Labels = mixedMoment B raw23231step2 raw23231step2Labels := by
      have ha : raw23231step2 = raw23231step1 := by apply Matrix.ext; unfold raw23231step2 raw23231step1; decide +kernel
      have hl : raw23231step1Labels = labelEmbedding6 ∘ raw23231step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23231step1 raw23231step1Labels raw23231step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw23232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23232step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23232 raw23232Labels = mixedMoment B node4292 node4292Labels := by
  calc
    mixedMoment B raw23232 raw23232Labels = mixedMoment B raw23232step0 raw23232step0Labels := by
      have ha : raw23232step0 = (fun i j => raw23232 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23232step0 raw23232; decide +kernel
      have hl : raw23232step0Labels = raw23232Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23232 raw23232Labels permutation176 permutation3
    mixedMoment B raw23232step0 raw23232step0Labels = mixedMoment B raw23232step1 raw23232step1Labels := by
      have ha : raw23232step1 = raw23232step0 := by apply Matrix.ext; unfold raw23232step1 raw23232step0; decide +kernel
      have hl : raw23232step0Labels = labelEmbedding6 ∘ raw23232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23232step0 raw23232step0Labels raw23232step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4292 node4292Labels := by rfl

def raw23233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23233step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23233step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23233 raw23233Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23233 raw23233Labels = mixedMoment B raw23233step0 raw23233step0Labels := by
      have hz : ∀ j, raw23233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23233step0 = (fun i j => raw23233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23233step0 raw23233; decide +kernel
      have hl : raw23233step0Labels = raw23233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23233 raw23233Labels permutation346 hz
    mixedMoment B raw23233step0 raw23233step0Labels = mixedMoment B raw23233step1 raw23233step1Labels := by
      have ha : raw23233step1 = (fun i j => raw23233step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23233step1 raw23233step0; decide +kernel
      have hl : raw23233step1Labels = raw23233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23233step0 raw23233step0Labels permutation36 permutation3
    mixedMoment B raw23233step1 raw23233step1Labels = mixedMoment B raw23233step2 raw23233step2Labels := by
      have ha : raw23233step2 = raw23233step1 := by apply Matrix.ext; unfold raw23233step2 raw23233step1; decide +kernel
      have hl : raw23233step1Labels = labelEmbedding6 ∘ raw23233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23233step1 raw23233step1Labels raw23233step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw23234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw23234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23234step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23234step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23234 raw23234Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw23234 raw23234Labels = mixedMoment B raw23234step0 raw23234step0Labels := by
      have hz : ∀ j, raw23234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23234step0 = (fun i j => raw23234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23234step0 raw23234; decide +kernel
      have hl : raw23234step0Labels = raw23234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23234 raw23234Labels permutation434 hz
    mixedMoment B raw23234step0 raw23234step0Labels = mixedMoment B raw23234step1 raw23234step1Labels := by
      have hz : ∀ j, raw23234step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23234step1 = (fun i j => raw23234step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23234step1 raw23234step0; decide +kernel
      have hl : raw23234step1Labels = raw23234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23234step0 raw23234step0Labels permutation80 hz
    mixedMoment B raw23234step1 raw23234step1Labels = mixedMoment B raw23234step2 raw23234step2Labels := by
      have ha : raw23234step2 = (fun i j => raw23234step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23234step2 raw23234step1; decide +kernel
      have hl : raw23234step2Labels = raw23234step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23234step1 raw23234step1Labels permutation9 permutation3
    mixedMoment B raw23234step2 raw23234step2Labels = mixedMoment B raw23234step3 raw23234step3Labels := by
      have ha : raw23234step3 = raw23234step2 := by apply Matrix.ext; unfold raw23234step3 raw23234step2; decide +kernel
      have hl : raw23234step2Labels = labelEmbedding6 ∘ raw23234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23234step2 raw23234step2Labels raw23234step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4110 node4110Labels := by rfl

def raw23235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw23235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23235step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23235 raw23235Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw23235 raw23235Labels = mixedMoment B raw23235step0 raw23235step0Labels := by
      have hz : ∀ j, raw23235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23235step0 = (fun i j => raw23235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23235step0 raw23235; decide +kernel
      have hl : raw23235step0Labels = raw23235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23235 raw23235Labels permutation434 hz
    mixedMoment B raw23235step0 raw23235step0Labels = mixedMoment B raw23235step1 raw23235step1Labels := by
      have hz : ∀ j, raw23235step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23235step1 = (fun i j => raw23235step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23235step1 raw23235step0; decide +kernel
      have hl : raw23235step1Labels = raw23235step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23235step0 raw23235step0Labels permutation80 hz
    mixedMoment B raw23235step1 raw23235step1Labels = mixedMoment B raw23235step2 raw23235step2Labels := by
      have ha : raw23235step2 = (fun i j => raw23235step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23235step2 raw23235step1; decide +kernel
      have hl : raw23235step2Labels = raw23235step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23235step1 raw23235step1Labels permutation9 permutation3
    mixedMoment B raw23235step2 raw23235step2Labels = mixedMoment B raw23235step3 raw23235step3Labels := by
      have ha : raw23235step3 = raw23235step2 := by apply Matrix.ext; unfold raw23235step3 raw23235step2; decide +kernel
      have hl : raw23235step2Labels = labelEmbedding6 ∘ raw23235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23235step2 raw23235step2Labels raw23235step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw23236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23236step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23236 raw23236Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw23236 raw23236Labels = mixedMoment B raw23236step0 raw23236step0Labels := by
      have hz : ∀ j, raw23236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23236step0 = (fun i j => raw23236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23236step0 raw23236; decide +kernel
      have hl : raw23236step0Labels = raw23236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23236 raw23236Labels permutation434 hz
    mixedMoment B raw23236step0 raw23236step0Labels = mixedMoment B raw23236step1 raw23236step1Labels := by
      have ha : raw23236step1 = (fun i j => raw23236step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23236step1 raw23236step0; decide +kernel
      have hl : raw23236step1Labels = raw23236step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23236step0 raw23236step0Labels permutation39 permutation3
    mixedMoment B raw23236step1 raw23236step1Labels = mixedMoment B raw23236step2 raw23236step2Labels := by
      have ha : raw23236step2 = raw23236step1 := by apply Matrix.ext; unfold raw23236step2 raw23236step1; decide +kernel
      have hl : raw23236step1Labels = labelEmbedding6 ∘ raw23236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23236step1 raw23236step1Labels raw23236step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

def raw23237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23237step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23237 raw23237Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw23237 raw23237Labels = mixedMoment B raw23237step0 raw23237step0Labels := by
      have hz : ∀ j, raw23237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23237step0 = (fun i j => raw23237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23237step0 raw23237; decide +kernel
      have hl : raw23237step0Labels = raw23237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23237 raw23237Labels permutation346 hz
    mixedMoment B raw23237step0 raw23237step0Labels = mixedMoment B raw23237step1 raw23237step1Labels := by
      have ha : raw23237step1 = (fun i j => raw23237step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23237step1 raw23237step0; decide +kernel
      have hl : raw23237step1Labels = raw23237step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23237step0 raw23237step0Labels permutation39 permutation3
    mixedMoment B raw23237step1 raw23237step1Labels = mixedMoment B raw23237step2 raw23237step2Labels := by
      have ha : raw23237step2 = raw23237step1 := by apply Matrix.ext; unfold raw23237step2 raw23237step1; decide +kernel
      have hl : raw23237step1Labels = labelEmbedding6 ∘ raw23237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23237step1 raw23237step1Labels raw23237step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

def raw23238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw23238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23238step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23238step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23238step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23238 raw23238Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw23238 raw23238Labels = mixedMoment B raw23238step0 raw23238step0Labels := by
      have hz : ∀ j, raw23238 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23238step0 = (fun i j => raw23238 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23238step0 raw23238; decide +kernel
      have hl : raw23238step0Labels = raw23238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23238 raw23238Labels permutation434 hz
    mixedMoment B raw23238step0 raw23238step0Labels = mixedMoment B raw23238step1 raw23238step1Labels := by
      have hz : ∀ j, raw23238step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23238step1 = (fun i j => raw23238step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23238step1 raw23238step0; decide +kernel
      have hl : raw23238step1Labels = raw23238step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23238step0 raw23238step0Labels permutation80 hz
    mixedMoment B raw23238step1 raw23238step1Labels = mixedMoment B raw23238step2 raw23238step2Labels := by
      have ha : raw23238step2 = (fun i j => raw23238step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23238step2 raw23238step1; decide +kernel
      have hl : raw23238step2Labels = raw23238step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23238step1 raw23238step1Labels permutation9 permutation3
    mixedMoment B raw23238step2 raw23238step2Labels = mixedMoment B raw23238step3 raw23238step3Labels := by
      have ha : raw23238step3 = raw23238step2 := by apply Matrix.ext; unfold raw23238step3 raw23238step2; decide +kernel
      have hl : raw23238step2Labels = labelEmbedding6 ∘ raw23238step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23238step2 raw23238step2Labels raw23238step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw23239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23239step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23239 raw23239Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw23239 raw23239Labels = mixedMoment B raw23239step0 raw23239step0Labels := by
      have hz : ∀ j, raw23239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23239step0 = (fun i j => raw23239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23239step0 raw23239; decide +kernel
      have hl : raw23239step0Labels = raw23239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23239 raw23239Labels permutation434 hz
    mixedMoment B raw23239step0 raw23239step0Labels = mixedMoment B raw23239step1 raw23239step1Labels := by
      have hz : ∀ j, raw23239step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23239step1 = (fun i j => raw23239step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23239step1 raw23239step0; decide +kernel
      have hl : raw23239step1Labels = raw23239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23239step0 raw23239step0Labels permutation80 hz
    mixedMoment B raw23239step1 raw23239step1Labels = mixedMoment B raw23239step2 raw23239step2Labels := by
      have ha : raw23239step2 = (fun i j => raw23239step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23239step2 raw23239step1; decide +kernel
      have hl : raw23239step2Labels = raw23239step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23239step1 raw23239step1Labels permutation8 permutation3
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw23240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23240 raw23240Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw23240 raw23240Labels = mixedMoment B raw23240step0 raw23240step0Labels := by
      have hz : ∀ j, raw23240 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23240step0 = (fun i j => raw23240 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23240step0 raw23240; decide +kernel
      have hl : raw23240step0Labels = raw23240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23240 raw23240Labels permutation434 hz
    mixedMoment B raw23240step0 raw23240step0Labels = mixedMoment B raw23240step1 raw23240step1Labels := by
      have ha : raw23240step1 = (fun i j => raw23240step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23240step1 raw23240step0; decide +kernel
      have hl : raw23240step1Labels = raw23240step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23240step0 raw23240step0Labels permutation38 permutation3
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw23241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23241 raw23241Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw23241 raw23241Labels = mixedMoment B raw23241step0 raw23241step0Labels := by
      have hz : ∀ j, raw23241 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23241step0 = (fun i j => raw23241 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23241step0 raw23241; decide +kernel
      have hl : raw23241step0Labels = raw23241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23241 raw23241Labels permutation346 hz
    mixedMoment B raw23241step0 raw23241step0Labels = mixedMoment B raw23241step1 raw23241step1Labels := by
      have ha : raw23241step1 = (fun i j => raw23241step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23241step1 raw23241step0; decide +kernel
      have hl : raw23241step1Labels = raw23241step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23241step0 raw23241step0Labels permutation38 permutation3
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw23242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw23242step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23242 raw23242Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw23242 raw23242Labels = mixedMoment B raw23242step0 raw23242step0Labels := by
      have hz : ∀ j, raw23242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23242step0 = (fun i j => raw23242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23242step0 raw23242; decide +kernel
      have hl : raw23242step0Labels = raw23242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23242 raw23242Labels permutation434 hz
    mixedMoment B raw23242step0 raw23242step0Labels = mixedMoment B raw23242step1 raw23242step1Labels := by
      have hz : ∀ j, raw23242step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23242step1 = (fun i j => raw23242step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23242step1 raw23242step0; decide +kernel
      have hl : raw23242step1Labels = raw23242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23242step0 raw23242step0Labels permutation80 hz
    mixedMoment B raw23242step1 raw23242step1Labels = mixedMoment B raw23242step2 raw23242step2Labels := by
      have ha : raw23242step2 = (fun i j => raw23242step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23242step2 raw23242step1; decide +kernel
      have hl : raw23242step2Labels = raw23242step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23242step1 raw23242step1Labels permutation9 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw23243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23243step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23243step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23243 raw23243Labels = mixedMoment B node563 node563Labels := by
  calc
    mixedMoment B raw23243 raw23243Labels = mixedMoment B raw23243step0 raw23243step0Labels := by
      have hz : ∀ j, raw23243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23243step0 = (fun i j => raw23243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23243step0 raw23243; decide +kernel
      have hl : raw23243step0Labels = raw23243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23243 raw23243Labels permutation434 hz
    mixedMoment B raw23243step0 raw23243step0Labels = mixedMoment B raw23243step1 raw23243step1Labels := by
      have hz : ∀ j, raw23243step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23243step1 = (fun i j => raw23243step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23243step1 raw23243step0; decide +kernel
      have hl : raw23243step1Labels = raw23243step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23243step0 raw23243step0Labels permutation80 hz
    mixedMoment B raw23243step1 raw23243step1Labels = mixedMoment B raw23243step2 raw23243step2Labels := by
      have ha : raw23243step2 = (fun i j => raw23243step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23243step2 raw23243step1; decide +kernel
      have hl : raw23243step2Labels = raw23243step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23243step1 raw23243step1Labels permutation8 permutation3
    _ = mixedMoment B node563 node563Labels := by rfl

def raw23244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23244step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23244 raw23244Labels = mixedMoment B node892 node892Labels := by
  calc
    mixedMoment B raw23244 raw23244Labels = mixedMoment B raw23244step0 raw23244step0Labels := by
      have hz : ∀ j, raw23244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23244step0 = (fun i j => raw23244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23244step0 raw23244; decide +kernel
      have hl : raw23244step0Labels = raw23244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23244 raw23244Labels permutation434 hz
    mixedMoment B raw23244step0 raw23244step0Labels = mixedMoment B raw23244step1 raw23244step1Labels := by
      have ha : raw23244step1 = (fun i j => raw23244step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23244step1 raw23244step0; decide +kernel
      have hl : raw23244step1Labels = raw23244step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23244step0 raw23244step0Labels permutation38 permutation3
    _ = mixedMoment B node892 node892Labels := by rfl

def raw23245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23245 raw23245Labels = mixedMoment B node892 node892Labels := by
  calc
    mixedMoment B raw23245 raw23245Labels = mixedMoment B raw23245step0 raw23245step0Labels := by
      have hz : ∀ j, raw23245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23245step0 = (fun i j => raw23245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23245step0 raw23245; decide +kernel
      have hl : raw23245step0Labels = raw23245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23245 raw23245Labels permutation346 hz
    mixedMoment B raw23245step0 raw23245step0Labels = mixedMoment B raw23245step1 raw23245step1Labels := by
      have ha : raw23245step1 = (fun i j => raw23245step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23245step1 raw23245step0; decide +kernel
      have hl : raw23245step1Labels = raw23245step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23245step0 raw23245step0Labels permutation38 permutation3
    _ = mixedMoment B node892 node892Labels := by rfl

def raw23246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw23246step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23246 raw23246Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw23246 raw23246Labels = mixedMoment B raw23246step0 raw23246step0Labels := by
      have hz : ∀ j, raw23246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23246step0 = (fun i j => raw23246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23246step0 raw23246; decide +kernel
      have hl : raw23246step0Labels = raw23246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23246 raw23246Labels permutation434 hz
    mixedMoment B raw23246step0 raw23246step0Labels = mixedMoment B raw23246step1 raw23246step1Labels := by
      have hz : ∀ j, raw23246step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23246step1 = (fun i j => raw23246step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23246step1 raw23246step0; decide +kernel
      have hl : raw23246step1Labels = raw23246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23246step0 raw23246step0Labels permutation80 hz
    mixedMoment B raw23246step1 raw23246step1Labels = mixedMoment B raw23246step2 raw23246step2Labels := by
      have ha : raw23246step2 = (fun i j => raw23246step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23246step2 raw23246step1; decide +kernel
      have hl : raw23246step2Labels = raw23246step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23246step1 raw23246step1Labels permutation12 permutation3
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw23247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23247 raw23247Labels = mixedMoment B node544 node544Labels := by
  calc
    mixedMoment B raw23247 raw23247Labels = mixedMoment B raw23247step0 raw23247step0Labels := by
      have hz : ∀ j, raw23247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23247step0 = (fun i j => raw23247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23247step0 raw23247; decide +kernel
      have hl : raw23247step0Labels = raw23247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23247 raw23247Labels permutation434 hz
    mixedMoment B raw23247step0 raw23247step0Labels = mixedMoment B raw23247step1 raw23247step1Labels := by
      have ha : raw23247step1 = (fun i j => raw23247step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23247step1 raw23247step0; decide +kernel
      have hl : raw23247step1Labels = raw23247step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23247step0 raw23247step0Labels permutation32 permutation3
    _ = mixedMoment B node544 node544Labels := by rfl

def raw23248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23248step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23248 raw23248Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw23248 raw23248Labels = mixedMoment B raw23248step0 raw23248step0Labels := by
      have hz : ∀ j, raw23248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23248step0 = (fun i j => raw23248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23248step0 raw23248; decide +kernel
      have hl : raw23248step0Labels = raw23248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23248 raw23248Labels permutation434 hz
    mixedMoment B raw23248step0 raw23248step0Labels = mixedMoment B raw23248step1 raw23248step1Labels := by
      have ha : raw23248step1 = (fun i j => raw23248step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23248step1 raw23248step0; decide +kernel
      have hl : raw23248step1Labels = raw23248step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23248step0 raw23248step0Labels permutation32 permutation3
    _ = mixedMoment B node933 node933Labels := by rfl

def raw23249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23249 raw23249Labels = mixedMoment B node870 node870Labels := by
  calc
    mixedMoment B raw23249 raw23249Labels = mixedMoment B raw23249step0 raw23249step0Labels := by
      have ha : raw23249step0 = (fun i j => raw23249 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23249step0 raw23249; decide +kernel
      have hl : raw23249step0Labels = raw23249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23249 raw23249Labels permutation200 permutation3
    _ = mixedMoment B node870 node870Labels := by rfl

def raw23250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23250 raw23250Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw23250 raw23250Labels = mixedMoment B raw23250step0 raw23250step0Labels := by
      have hz : ∀ j, raw23250 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23250step0 = (fun i j => raw23250 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23250step0 raw23250; decide +kernel
      have hl : raw23250step0Labels = raw23250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23250 raw23250Labels permutation434 hz
    mixedMoment B raw23250step0 raw23250step0Labels = mixedMoment B raw23250step1 raw23250step1Labels := by
      have ha : raw23250step1 = (fun i j => raw23250step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23250step1 raw23250step0; decide +kernel
      have hl : raw23250step1Labels = raw23250step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23250step0 raw23250step0Labels permutation36 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw23251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23251 raw23251Labels = mixedMoment B node544 node544Labels := by
  calc
    mixedMoment B raw23251 raw23251Labels = mixedMoment B raw23251step0 raw23251step0Labels := by
      have hz : ∀ j, raw23251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23251step0 = (fun i j => raw23251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23251step0 raw23251; decide +kernel
      have hl : raw23251step0Labels = raw23251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23251 raw23251Labels permutation346 hz
    mixedMoment B raw23251step0 raw23251step0Labels = mixedMoment B raw23251step1 raw23251step1Labels := by
      have ha : raw23251step1 = (fun i j => raw23251step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23251step1 raw23251step0; decide +kernel
      have hl : raw23251step1Labels = raw23251step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23251step0 raw23251step0Labels permutation32 permutation3
    _ = mixedMoment B node544 node544Labels := by rfl

def raw23252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23252 raw23252Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw23252 raw23252Labels = mixedMoment B raw23252step0 raw23252step0Labels := by
      have hz : ∀ j, raw23252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23252step0 = (fun i j => raw23252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23252step0 raw23252; decide +kernel
      have hl : raw23252step0Labels = raw23252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23252 raw23252Labels permutation346 hz
    mixedMoment B raw23252step0 raw23252step0Labels = mixedMoment B raw23252step1 raw23252step1Labels := by
      have ha : raw23252step1 = (fun i j => raw23252step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23252step1 raw23252step0; decide +kernel
      have hl : raw23252step1Labels = raw23252step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23252step0 raw23252step0Labels permutation32 permutation3
    _ = mixedMoment B node933 node933Labels := by rfl

def raw23253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23253 raw23253Labels = mixedMoment B node870 node870Labels := by
  calc
    mixedMoment B raw23253 raw23253Labels = mixedMoment B raw23253step0 raw23253step0Labels := by
      have ha : raw23253step0 = (fun i j => raw23253 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23253step0 raw23253; decide +kernel
      have hl : raw23253step0Labels = raw23253Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23253 raw23253Labels permutation176 permutation3
    _ = mixedMoment B node870 node870Labels := by rfl

def raw23254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23254 raw23254Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw23254 raw23254Labels = mixedMoment B raw23254step0 raw23254step0Labels := by
      have hz : ∀ j, raw23254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23254step0 = (fun i j => raw23254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23254step0 raw23254; decide +kernel
      have hl : raw23254step0Labels = raw23254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23254 raw23254Labels permutation346 hz
    mixedMoment B raw23254step0 raw23254step0Labels = mixedMoment B raw23254step1 raw23254step1Labels := by
      have ha : raw23254step1 = (fun i j => raw23254step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23254step1 raw23254step0; decide +kernel
      have hl : raw23254step1Labels = raw23254step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23254step0 raw23254step0Labels permutation36 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw23255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23255step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw23255step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23255 raw23255Labels = mixedMoment B node547 node547Labels := by
  calc
    mixedMoment B raw23255 raw23255Labels = mixedMoment B raw23255step0 raw23255step0Labels := by
      have hz : ∀ j, raw23255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23255step0 = (fun i j => raw23255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23255step0 raw23255; decide +kernel
      have hl : raw23255step0Labels = raw23255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23255 raw23255Labels permutation434 hz
    mixedMoment B raw23255step0 raw23255step0Labels = mixedMoment B raw23255step1 raw23255step1Labels := by
      have hz : ∀ j, raw23255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23255step1 = (fun i j => raw23255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23255step1 raw23255step0; decide +kernel
      have hl : raw23255step1Labels = raw23255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23255step0 raw23255step0Labels permutation80 hz
    mixedMoment B raw23255step1 raw23255step1Labels = mixedMoment B raw23255step2 raw23255step2Labels := by
      have ha : raw23255step2 = (fun i j => raw23255step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23255step2 raw23255step1; decide +kernel
      have hl : raw23255step2Labels = raw23255step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23255step1 raw23255step1Labels permutation9 permutation3
    _ = mixedMoment B node547 node547Labels := by rfl

def raw23256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw23256step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23256 raw23256Labels = mixedMoment B node938 node938Labels := by
  calc
    mixedMoment B raw23256 raw23256Labels = mixedMoment B raw23256step0 raw23256step0Labels := by
      have hz : ∀ j, raw23256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23256step0 = (fun i j => raw23256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23256step0 raw23256; decide +kernel
      have hl : raw23256step0Labels = raw23256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23256 raw23256Labels permutation434 hz
    mixedMoment B raw23256step0 raw23256step0Labels = mixedMoment B raw23256step1 raw23256step1Labels := by
      have hz : ∀ j, raw23256step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23256step1 = (fun i j => raw23256step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23256step1 raw23256step0; decide +kernel
      have hl : raw23256step1Labels = raw23256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23256step0 raw23256step0Labels permutation80 hz
    mixedMoment B raw23256step1 raw23256step1Labels = mixedMoment B raw23256step2 raw23256step2Labels := by
      have ha : raw23256step2 = (fun i j => raw23256step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23256step2 raw23256step1; decide +kernel
      have hl : raw23256step2Labels = raw23256step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23256step1 raw23256step1Labels permutation9 permutation3
    _ = mixedMoment B node938 node938Labels := by rfl

def raw23257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23257step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23257 raw23257Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw23257 raw23257Labels = mixedMoment B raw23257step0 raw23257step0Labels := by
      have hz : ∀ j, raw23257 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23257step0 = (fun i j => raw23257 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23257step0 raw23257; decide +kernel
      have hl : raw23257step0Labels = raw23257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23257 raw23257Labels permutation434 hz
    mixedMoment B raw23257step0 raw23257step0Labels = mixedMoment B raw23257step1 raw23257step1Labels := by
      have ha : raw23257step1 = (fun i j => raw23257step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23257step1 raw23257step0; decide +kernel
      have hl : raw23257step1Labels = raw23257step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23257step0 raw23257step0Labels permutation39 permutation3
    _ = mixedMoment B node873 node873Labels := by rfl

def raw23258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23258 raw23258Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw23258 raw23258Labels = mixedMoment B raw23258step0 raw23258step0Labels := by
      have hz : ∀ j, raw23258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23258step0 = (fun i j => raw23258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23258step0 raw23258; decide +kernel
      have hl : raw23258step0Labels = raw23258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23258 raw23258Labels permutation346 hz
    mixedMoment B raw23258step0 raw23258step0Labels = mixedMoment B raw23258step1 raw23258step1Labels := by
      have ha : raw23258step1 = (fun i j => raw23258step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23258step1 raw23258step0; decide +kernel
      have hl : raw23258step1Labels = raw23258step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23258step0 raw23258step0Labels permutation39 permutation3
    _ = mixedMoment B node873 node873Labels := by rfl

def raw23259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23259step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw23259step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23259 raw23259Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw23259 raw23259Labels = mixedMoment B raw23259step0 raw23259step0Labels := by
      have hz : ∀ j, raw23259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23259step0 = (fun i j => raw23259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23259step0 raw23259; decide +kernel
      have hl : raw23259step0Labels = raw23259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23259 raw23259Labels permutation434 hz
    mixedMoment B raw23259step0 raw23259step0Labels = mixedMoment B raw23259step1 raw23259step1Labels := by
      have hz : ∀ j, raw23259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23259step1 = (fun i j => raw23259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23259step1 raw23259step0; decide +kernel
      have hl : raw23259step1Labels = raw23259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23259step0 raw23259step0Labels permutation80 hz
    mixedMoment B raw23259step1 raw23259step1Labels = mixedMoment B raw23259step2 raw23259step2Labels := by
      have ha : raw23259step2 = (fun i j => raw23259step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23259step2 raw23259step1; decide +kernel
      have hl : raw23259step2Labels = raw23259step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23259step1 raw23259step1Labels permutation9 permutation3
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw23260 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23260step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23260step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23260 raw23260Labels = mixedMoment B node4279 node4279Labels := by
  calc
    mixedMoment B raw23260 raw23260Labels = mixedMoment B raw23260step0 raw23260step0Labels := by
      have hz : ∀ j, raw23260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23260step0 = (fun i j => raw23260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23260step0 raw23260; decide +kernel
      have hl : raw23260step0Labels = raw23260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23260 raw23260Labels permutation434 hz
    mixedMoment B raw23260step0 raw23260step0Labels = mixedMoment B raw23260step1 raw23260step1Labels := by
      have hz : ∀ j, raw23260step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23260step1 = (fun i j => raw23260step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23260step1 raw23260step0; decide +kernel
      have hl : raw23260step1Labels = raw23260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23260step0 raw23260step0Labels permutation80 hz
    mixedMoment B raw23260step1 raw23260step1Labels = mixedMoment B raw23260step2 raw23260step2Labels := by
      have ha : raw23260step2 = (fun i j => raw23260step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23260step2 raw23260step1; decide +kernel
      have hl : raw23260step2Labels = raw23260step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23260step1 raw23260step1Labels permutation8 permutation6
    mixedMoment B raw23260step2 raw23260step2Labels = mixedMoment B raw23260step3 raw23260step3Labels := by
      have ha : raw23260step3 = raw23260step2 := by apply Matrix.ext; unfold raw23260step3 raw23260step2; decide +kernel
      have hl : raw23260step2Labels = labelEmbedding9 ∘ raw23260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23260step2 raw23260step2Labels raw23260step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4279 node4279Labels := by rfl

def raw23261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23261step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23261 raw23261Labels = mixedMoment B node4412 node4412Labels := by
  calc
    mixedMoment B raw23261 raw23261Labels = mixedMoment B raw23261step0 raw23261step0Labels := by
      have hz : ∀ j, raw23261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23261step0 = (fun i j => raw23261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23261step0 raw23261; decide +kernel
      have hl : raw23261step0Labels = raw23261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23261 raw23261Labels permutation434 hz
    mixedMoment B raw23261step0 raw23261step0Labels = mixedMoment B raw23261step1 raw23261step1Labels := by
      have ha : raw23261step1 = (fun i j => raw23261step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23261step1 raw23261step0; decide +kernel
      have hl : raw23261step1Labels = raw23261step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23261step0 raw23261step0Labels permutation38 permutation6
    mixedMoment B raw23261step1 raw23261step1Labels = mixedMoment B raw23261step2 raw23261step2Labels := by
      have ha : raw23261step2 = raw23261step1 := by apply Matrix.ext; unfold raw23261step2 raw23261step1; decide +kernel
      have hl : raw23261step1Labels = labelEmbedding9 ∘ raw23261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23261step1 raw23261step1Labels raw23261step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4412 node4412Labels := by rfl

def raw23262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23262step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23262 raw23262Labels = mixedMoment B node4412 node4412Labels := by
  calc
    mixedMoment B raw23262 raw23262Labels = mixedMoment B raw23262step0 raw23262step0Labels := by
      have hz : ∀ j, raw23262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23262step0 = (fun i j => raw23262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23262step0 raw23262; decide +kernel
      have hl : raw23262step0Labels = raw23262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23262 raw23262Labels permutation346 hz
    mixedMoment B raw23262step0 raw23262step0Labels = mixedMoment B raw23262step1 raw23262step1Labels := by
      have ha : raw23262step1 = (fun i j => raw23262step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23262step1 raw23262step0; decide +kernel
      have hl : raw23262step1Labels = raw23262step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23262step0 raw23262step0Labels permutation38 permutation6
    mixedMoment B raw23262step1 raw23262step1Labels = mixedMoment B raw23262step2 raw23262step2Labels := by
      have ha : raw23262step2 = raw23262step1 := by apply Matrix.ext; unfold raw23262step2 raw23262step1; decide +kernel
      have hl : raw23262step1Labels = labelEmbedding9 ∘ raw23262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23262step1 raw23262step1Labels raw23262step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4412 node4412Labels := by rfl

def raw23263 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23263step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23263 raw23263Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw23263 raw23263Labels = mixedMoment B raw23263step0 raw23263step0Labels := by
      have hz : ∀ j, raw23263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23263step0 = (fun i j => raw23263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23263step0 raw23263; decide +kernel
      have hl : raw23263step0Labels = raw23263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23263 raw23263Labels permutation434 hz
    mixedMoment B raw23263step0 raw23263step0Labels = mixedMoment B raw23263step1 raw23263step1Labels := by
      have hz : ∀ j, raw23263step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23263step1 = (fun i j => raw23263step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23263step1 raw23263step0; decide +kernel
      have hl : raw23263step1Labels = raw23263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23263step0 raw23263step0Labels permutation80 hz
    mixedMoment B raw23263step1 raw23263step1Labels = mixedMoment B raw23263step2 raw23263step2Labels := by
      have ha : raw23263step2 = (fun i j => raw23263step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23263step2 raw23263step1; decide +kernel
      have hl : raw23263step2Labels = raw23263step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23263step1 raw23263step1Labels permutation8 permutation6
    mixedMoment B raw23263step2 raw23263step2Labels = mixedMoment B raw23263step3 raw23263step3Labels := by
      have ha : raw23263step3 = raw23263step2 := by apply Matrix.ext; unfold raw23263step3 raw23263step2; decide +kernel
      have hl : raw23263step2Labels = labelEmbedding9 ∘ raw23263step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23263step2 raw23263step2Labels raw23263step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw23264 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23264step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23264 raw23264Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw23264 raw23264Labels = mixedMoment B raw23264step0 raw23264step0Labels := by
      have hz : ∀ j, raw23264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23264step0 = (fun i j => raw23264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23264step0 raw23264; decide +kernel
      have hl : raw23264step0Labels = raw23264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23264 raw23264Labels permutation434 hz
    mixedMoment B raw23264step0 raw23264step0Labels = mixedMoment B raw23264step1 raw23264step1Labels := by
      have ha : raw23264step1 = (fun i j => raw23264step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23264step1 raw23264step0; decide +kernel
      have hl : raw23264step1Labels = raw23264step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23264step0 raw23264step0Labels permutation32 permutation6
    mixedMoment B raw23264step1 raw23264step1Labels = mixedMoment B raw23264step2 raw23264step2Labels := by
      have ha : raw23264step2 = raw23264step1 := by apply Matrix.ext; unfold raw23264step2 raw23264step1; decide +kernel
      have hl : raw23264step1Labels = labelEmbedding9 ∘ raw23264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23264step1 raw23264step1Labels raw23264step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

def raw23265 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23265step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23265 raw23265Labels = mixedMoment B node4393 node4393Labels := by
  calc
    mixedMoment B raw23265 raw23265Labels = mixedMoment B raw23265step0 raw23265step0Labels := by
      have ha : raw23265step0 = (fun i j => raw23265 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23265step0 raw23265; decide +kernel
      have hl : raw23265step0Labels = raw23265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23265 raw23265Labels permutation200 permutation6
    mixedMoment B raw23265step0 raw23265step0Labels = mixedMoment B raw23265step1 raw23265step1Labels := by
      have ha : raw23265step1 = raw23265step0 := by apply Matrix.ext; unfold raw23265step1 raw23265step0; decide +kernel
      have hl : raw23265step0Labels = labelEmbedding9 ∘ raw23265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23265step0 raw23265step0Labels raw23265step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4393 node4393Labels := by rfl

def raw23266 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23266step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23266 raw23266Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw23266 raw23266Labels = mixedMoment B raw23266step0 raw23266step0Labels := by
      have hz : ∀ j, raw23266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23266step0 = (fun i j => raw23266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23266step0 raw23266; decide +kernel
      have hl : raw23266step0Labels = raw23266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23266 raw23266Labels permutation434 hz
    mixedMoment B raw23266step0 raw23266step0Labels = mixedMoment B raw23266step1 raw23266step1Labels := by
      have ha : raw23266step1 = (fun i j => raw23266step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23266step1 raw23266step0; decide +kernel
      have hl : raw23266step1Labels = raw23266step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23266step0 raw23266step0Labels permutation32 permutation6
    mixedMoment B raw23266step1 raw23266step1Labels = mixedMoment B raw23266step2 raw23266step2Labels := by
      have ha : raw23266step2 = raw23266step1 := by apply Matrix.ext; unfold raw23266step2 raw23266step1; decide +kernel
      have hl : raw23266step1Labels = labelEmbedding9 ∘ raw23266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23266step1 raw23266step1Labels raw23266step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw23267 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23267step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23267 raw23267Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw23267 raw23267Labels = mixedMoment B raw23267step0 raw23267step0Labels := by
      have hz : ∀ j, raw23267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23267step0 = (fun i j => raw23267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23267step0 raw23267; decide +kernel
      have hl : raw23267step0Labels = raw23267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23267 raw23267Labels permutation346 hz
    mixedMoment B raw23267step0 raw23267step0Labels = mixedMoment B raw23267step1 raw23267step1Labels := by
      have ha : raw23267step1 = (fun i j => raw23267step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23267step1 raw23267step0; decide +kernel
      have hl : raw23267step1Labels = raw23267step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23267step0 raw23267step0Labels permutation32 permutation6
    mixedMoment B raw23267step1 raw23267step1Labels = mixedMoment B raw23267step2 raw23267step2Labels := by
      have ha : raw23267step2 = raw23267step1 := by apply Matrix.ext; unfold raw23267step2 raw23267step1; decide +kernel
      have hl : raw23267step1Labels = labelEmbedding9 ∘ raw23267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23267step1 raw23267step1Labels raw23267step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

def raw23268 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23268step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23268 raw23268Labels = mixedMoment B node4393 node4393Labels := by
  calc
    mixedMoment B raw23268 raw23268Labels = mixedMoment B raw23268step0 raw23268step0Labels := by
      have ha : raw23268step0 = (fun i j => raw23268 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23268step0 raw23268; decide +kernel
      have hl : raw23268step0Labels = raw23268Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23268 raw23268Labels permutation176 permutation6
    mixedMoment B raw23268step0 raw23268step0Labels = mixedMoment B raw23268step1 raw23268step1Labels := by
      have ha : raw23268step1 = raw23268step0 := by apply Matrix.ext; unfold raw23268step1 raw23268step0; decide +kernel
      have hl : raw23268step0Labels = labelEmbedding9 ∘ raw23268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23268step0 raw23268step0Labels raw23268step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4393 node4393Labels := by rfl

def raw23269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23269step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23269 raw23269Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw23269 raw23269Labels = mixedMoment B raw23269step0 raw23269step0Labels := by
      have hz : ∀ j, raw23269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23269step0 = (fun i j => raw23269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23269step0 raw23269; decide +kernel
      have hl : raw23269step0Labels = raw23269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23269 raw23269Labels permutation346 hz
    mixedMoment B raw23269step0 raw23269step0Labels = mixedMoment B raw23269step1 raw23269step1Labels := by
      have ha : raw23269step1 = (fun i j => raw23269step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23269step1 raw23269step0; decide +kernel
      have hl : raw23269step1Labels = raw23269step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23269step0 raw23269step0Labels permutation32 permutation6
    mixedMoment B raw23269step1 raw23269step1Labels = mixedMoment B raw23269step2 raw23269step2Labels := by
      have ha : raw23269step2 = raw23269step1 := by apply Matrix.ext; unfold raw23269step2 raw23269step1; decide +kernel
      have hl : raw23269step1Labels = labelEmbedding9 ∘ raw23269step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23269step1 raw23269step1Labels raw23269step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw23270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23270step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23270step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23270step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23270 raw23270Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw23270 raw23270Labels = mixedMoment B raw23270step0 raw23270step0Labels := by
      have hz : ∀ j, raw23270 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23270step0 = (fun i j => raw23270 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23270step0 raw23270; decide +kernel
      have hl : raw23270step0Labels = raw23270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23270 raw23270Labels permutation434 hz
    mixedMoment B raw23270step0 raw23270step0Labels = mixedMoment B raw23270step1 raw23270step1Labels := by
      have hz : ∀ j, raw23270step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23270step1 = (fun i j => raw23270step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23270step1 raw23270step0; decide +kernel
      have hl : raw23270step1Labels = raw23270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23270step0 raw23270step0Labels permutation80 hz
    mixedMoment B raw23270step1 raw23270step1Labels = mixedMoment B raw23270step2 raw23270step2Labels := by
      have ha : raw23270step2 = (fun i j => raw23270step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23270step2 raw23270step1; decide +kernel
      have hl : raw23270step2Labels = raw23270step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23270step1 raw23270step1Labels permutation9 permutation6
    mixedMoment B raw23270step2 raw23270step2Labels = mixedMoment B raw23270step3 raw23270step3Labels := by
      have ha : raw23270step3 = raw23270step2 := by apply Matrix.ext; unfold raw23270step3 raw23270step2; decide +kernel
      have hl : raw23270step2Labels = labelEmbedding9 ∘ raw23270step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23270step2 raw23270step2Labels raw23270step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw23271 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23271step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23271step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23271step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23271 raw23271Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw23271 raw23271Labels = mixedMoment B raw23271step0 raw23271step0Labels := by
      have hz : ∀ j, raw23271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23271step0 = (fun i j => raw23271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23271step0 raw23271; decide +kernel
      have hl : raw23271step0Labels = raw23271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23271 raw23271Labels permutation434 hz
    mixedMoment B raw23271step0 raw23271step0Labels = mixedMoment B raw23271step1 raw23271step1Labels := by
      have hz : ∀ j, raw23271step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23271step1 = (fun i j => raw23271step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23271step1 raw23271step0; decide +kernel
      have hl : raw23271step1Labels = raw23271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23271step0 raw23271step0Labels permutation80 hz
    mixedMoment B raw23271step1 raw23271step1Labels = mixedMoment B raw23271step2 raw23271step2Labels := by
      have ha : raw23271step2 = (fun i j => raw23271step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23271step2 raw23271step1; decide +kernel
      have hl : raw23271step2Labels = raw23271step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23271step1 raw23271step1Labels permutation8 permutation6
    mixedMoment B raw23271step2 raw23271step2Labels = mixedMoment B raw23271step3 raw23271step3Labels := by
      have ha : raw23271step3 = raw23271step2 := by apply Matrix.ext; unfold raw23271step3 raw23271step2; decide +kernel
      have hl : raw23271step2Labels = labelEmbedding9 ∘ raw23271step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23271step2 raw23271step2Labels raw23271step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw23272 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23272step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23272 raw23272Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw23272 raw23272Labels = mixedMoment B raw23272step0 raw23272step0Labels := by
      have hz : ∀ j, raw23272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23272step0 = (fun i j => raw23272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23272step0 raw23272; decide +kernel
      have hl : raw23272step0Labels = raw23272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23272 raw23272Labels permutation434 hz
    mixedMoment B raw23272step0 raw23272step0Labels = mixedMoment B raw23272step1 raw23272step1Labels := by
      have ha : raw23272step1 = (fun i j => raw23272step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23272step1 raw23272step0; decide +kernel
      have hl : raw23272step1Labels = raw23272step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23272step0 raw23272step0Labels permutation38 permutation6
    mixedMoment B raw23272step1 raw23272step1Labels = mixedMoment B raw23272step2 raw23272step2Labels := by
      have ha : raw23272step2 = raw23272step1 := by apply Matrix.ext; unfold raw23272step2 raw23272step1; decide +kernel
      have hl : raw23272step1Labels = labelEmbedding9 ∘ raw23272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23272step1 raw23272step1Labels raw23272step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw23273 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23273step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23273 raw23273Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw23273 raw23273Labels = mixedMoment B raw23273step0 raw23273step0Labels := by
      have hz : ∀ j, raw23273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23273step0 = (fun i j => raw23273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23273step0 raw23273; decide +kernel
      have hl : raw23273step0Labels = raw23273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23273 raw23273Labels permutation346 hz
    mixedMoment B raw23273step0 raw23273step0Labels = mixedMoment B raw23273step1 raw23273step1Labels := by
      have ha : raw23273step1 = (fun i j => raw23273step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23273step1 raw23273step0; decide +kernel
      have hl : raw23273step1Labels = raw23273step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23273step0 raw23273step0Labels permutation38 permutation6
    mixedMoment B raw23273step1 raw23273step1Labels = mixedMoment B raw23273step2 raw23273step2Labels := by
      have ha : raw23273step2 = raw23273step1 := by apply Matrix.ext; unfold raw23273step2 raw23273step1; decide +kernel
      have hl : raw23273step1Labels = labelEmbedding9 ∘ raw23273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23273step1 raw23273step1Labels raw23273step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw23274 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23274step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23274 raw23274Labels = mixedMoment B node831 node831Labels := by
  calc
    mixedMoment B raw23274 raw23274Labels = mixedMoment B raw23274step0 raw23274step0Labels := by
      have hz : ∀ j, raw23274 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23274step0 = (fun i j => raw23274 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23274step0 raw23274; decide +kernel
      have hl : raw23274step0Labels = raw23274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23274 raw23274Labels permutation434 hz
    mixedMoment B raw23274step0 raw23274step0Labels = mixedMoment B raw23274step1 raw23274step1Labels := by
      have hz : ∀ j, raw23274step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23274step1 = (fun i j => raw23274step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23274step1 raw23274step0; decide +kernel
      have hl : raw23274step1Labels = raw23274step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23274step0 raw23274step0Labels permutation80 hz
    mixedMoment B raw23274step1 raw23274step1Labels = mixedMoment B raw23274step2 raw23274step2Labels := by
      have ha : raw23274step2 = (fun i j => raw23274step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23274step2 raw23274step1; decide +kernel
      have hl : raw23274step2Labels = raw23274step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23274step1 raw23274step1Labels permutation8 permutation6
    _ = mixedMoment B node831 node831Labels := by rfl

def raw23275 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23275 raw23275Labels = mixedMoment B node993 node993Labels := by
  calc
    mixedMoment B raw23275 raw23275Labels = mixedMoment B raw23275step0 raw23275step0Labels := by
      have hz : ∀ j, raw23275 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23275step0 = (fun i j => raw23275 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23275step0 raw23275; decide +kernel
      have hl : raw23275step0Labels = raw23275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23275 raw23275Labels permutation434 hz
    mixedMoment B raw23275step0 raw23275step0Labels = mixedMoment B raw23275step1 raw23275step1Labels := by
      have ha : raw23275step1 = (fun i j => raw23275step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23275step1 raw23275step0; decide +kernel
      have hl : raw23275step1Labels = raw23275step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23275step0 raw23275step0Labels permutation38 permutation6
    _ = mixedMoment B node993 node993Labels := by rfl

def raw23276 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23276 raw23276Labels = mixedMoment B node993 node993Labels := by
  calc
    mixedMoment B raw23276 raw23276Labels = mixedMoment B raw23276step0 raw23276step0Labels := by
      have hz : ∀ j, raw23276 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23276step0 = (fun i j => raw23276 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23276step0 raw23276; decide +kernel
      have hl : raw23276step0Labels = raw23276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23276 raw23276Labels permutation346 hz
    mixedMoment B raw23276step0 raw23276step0Labels = mixedMoment B raw23276step1 raw23276step1Labels := by
      have ha : raw23276step1 = (fun i j => raw23276step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23276step1 raw23276step0; decide +kernel
      have hl : raw23276step1Labels = raw23276step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23276step0 raw23276step0Labels permutation38 permutation6
    _ = mixedMoment B node993 node993Labels := by rfl

def raw23277 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23277step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23277 raw23277Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw23277 raw23277Labels = mixedMoment B raw23277step0 raw23277step0Labels := by
      have hz : ∀ j, raw23277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23277step0 = (fun i j => raw23277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23277step0 raw23277; decide +kernel
      have hl : raw23277step0Labels = raw23277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23277 raw23277Labels permutation434 hz
    mixedMoment B raw23277step0 raw23277step0Labels = mixedMoment B raw23277step1 raw23277step1Labels := by
      have hz : ∀ j, raw23277step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23277step1 = (fun i j => raw23277step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23277step1 raw23277step0; decide +kernel
      have hl : raw23277step1Labels = raw23277step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23277step0 raw23277step0Labels permutation80 hz
    mixedMoment B raw23277step1 raw23277step1Labels = mixedMoment B raw23277step2 raw23277step2Labels := by
      have ha : raw23277step2 = (fun i j => raw23277step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23277step2 raw23277step1; decide +kernel
      have hl : raw23277step2Labels = raw23277step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23277step1 raw23277step1Labels permutation8 permutation6
    _ = mixedMoment B node1063 node1063Labels := by rfl

def raw23278 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23278 raw23278Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw23278 raw23278Labels = mixedMoment B raw23278step0 raw23278step0Labels := by
      have hz : ∀ j, raw23278 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23278step0 = (fun i j => raw23278 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23278step0 raw23278; decide +kernel
      have hl : raw23278step0Labels = raw23278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23278 raw23278Labels permutation434 hz
    mixedMoment B raw23278step0 raw23278step0Labels = mixedMoment B raw23278step1 raw23278step1Labels := by
      have ha : raw23278step1 = (fun i j => raw23278step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23278step1 raw23278step0; decide +kernel
      have hl : raw23278step1Labels = raw23278step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23278step0 raw23278step0Labels permutation32 permutation6
    _ = mixedMoment B node790 node790Labels := by rfl

def raw23279 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23279 raw23279Labels = mixedMoment B node974 node974Labels := by
  calc
    mixedMoment B raw23279 raw23279Labels = mixedMoment B raw23279step0 raw23279step0Labels := by
      have ha : raw23279step0 = (fun i j => raw23279 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23279step0 raw23279; decide +kernel
      have hl : raw23279step0Labels = raw23279Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23279 raw23279Labels permutation200 permutation6
    _ = mixedMoment B node974 node974Labels := by rfl

def raw23280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23280 raw23280Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw23280 raw23280Labels = mixedMoment B raw23280step0 raw23280step0Labels := by
      have hz : ∀ j, raw23280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23280step0 = (fun i j => raw23280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23280step0 raw23280; decide +kernel
      have hl : raw23280step0Labels = raw23280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23280 raw23280Labels permutation434 hz
    mixedMoment B raw23280step0 raw23280step0Labels = mixedMoment B raw23280step1 raw23280step1Labels := by
      have ha : raw23280step1 = (fun i j => raw23280step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23280step1 raw23280step0; decide +kernel
      have hl : raw23280step1Labels = raw23280step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23280step0 raw23280step0Labels permutation32 permutation6
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw23281 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23281step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23281step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23281 raw23281Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw23281 raw23281Labels = mixedMoment B raw23281step0 raw23281step0Labels := by
      have hz : ∀ j, raw23281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23281step0 = (fun i j => raw23281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23281step0 raw23281; decide +kernel
      have hl : raw23281step0Labels = raw23281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23281 raw23281Labels permutation346 hz
    mixedMoment B raw23281step0 raw23281step0Labels = mixedMoment B raw23281step1 raw23281step1Labels := by
      have ha : raw23281step1 = (fun i j => raw23281step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23281step1 raw23281step0; decide +kernel
      have hl : raw23281step1Labels = raw23281step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23281step0 raw23281step0Labels permutation32 permutation6
    _ = mixedMoment B node790 node790Labels := by rfl

def raw23282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23282step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23282 raw23282Labels = mixedMoment B node974 node974Labels := by
  calc
    mixedMoment B raw23282 raw23282Labels = mixedMoment B raw23282step0 raw23282step0Labels := by
      have ha : raw23282step0 = (fun i j => raw23282 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23282step0 raw23282; decide +kernel
      have hl : raw23282step0Labels = raw23282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23282 raw23282Labels permutation176 permutation6
    _ = mixedMoment B node974 node974Labels := by rfl

def raw23283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23283 raw23283Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw23283 raw23283Labels = mixedMoment B raw23283step0 raw23283step0Labels := by
      have hz : ∀ j, raw23283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23283step0 = (fun i j => raw23283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23283step0 raw23283; decide +kernel
      have hl : raw23283step0Labels = raw23283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23283 raw23283Labels permutation346 hz
    mixedMoment B raw23283step0 raw23283step0Labels = mixedMoment B raw23283step1 raw23283step1Labels := by
      have ha : raw23283step1 = (fun i j => raw23283step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23283step1 raw23283step0; decide +kernel
      have hl : raw23283step1Labels = raw23283step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23283step0 raw23283step0Labels permutation32 permutation6
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw23284 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23284step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23284 raw23284Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw23284 raw23284Labels = mixedMoment B raw23284step0 raw23284step0Labels := by
      have hz : ∀ j, raw23284 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23284step0 = (fun i j => raw23284 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23284step0 raw23284; decide +kernel
      have hl : raw23284step0Labels = raw23284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23284 raw23284Labels permutation434 hz
    mixedMoment B raw23284step0 raw23284step0Labels = mixedMoment B raw23284step1 raw23284step1Labels := by
      have hz : ∀ j, raw23284step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23284step1 = (fun i j => raw23284step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23284step1 raw23284step0; decide +kernel
      have hl : raw23284step1Labels = raw23284step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23284step0 raw23284step0Labels permutation80 hz
    mixedMoment B raw23284step1 raw23284step1Labels = mixedMoment B raw23284step2 raw23284step2Labels := by
      have ha : raw23284step2 = (fun i j => raw23284step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23284step2 raw23284step1; decide +kernel
      have hl : raw23284step2Labels = raw23284step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23284step1 raw23284step1Labels permutation9 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw23285 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23285step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23285 raw23285Labels = mixedMoment B node816 node816Labels := by
  calc
    mixedMoment B raw23285 raw23285Labels = mixedMoment B raw23285step0 raw23285step0Labels := by
      have hz : ∀ j, raw23285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23285step0 = (fun i j => raw23285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23285step0 raw23285; decide +kernel
      have hl : raw23285step0Labels = raw23285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23285 raw23285Labels permutation434 hz
    mixedMoment B raw23285step0 raw23285step0Labels = mixedMoment B raw23285step1 raw23285step1Labels := by
      have hz : ∀ j, raw23285step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23285step1 = (fun i j => raw23285step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23285step1 raw23285step0; decide +kernel
      have hl : raw23285step1Labels = raw23285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23285step0 raw23285step0Labels permutation80 hz
    mixedMoment B raw23285step1 raw23285step1Labels = mixedMoment B raw23285step2 raw23285step2Labels := by
      have ha : raw23285step2 = (fun i j => raw23285step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23285step2 raw23285step1; decide +kernel
      have hl : raw23285step2Labels = raw23285step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23285step1 raw23285step1Labels permutation8 permutation6
    _ = mixedMoment B node816 node816Labels := by rfl

def raw23286 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23286step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23286 raw23286Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw23286 raw23286Labels = mixedMoment B raw23286step0 raw23286step0Labels := by
      have hz : ∀ j, raw23286 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23286step0 = (fun i j => raw23286 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23286step0 raw23286; decide +kernel
      have hl : raw23286step0Labels = raw23286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23286 raw23286Labels permutation434 hz
    mixedMoment B raw23286step0 raw23286step0Labels = mixedMoment B raw23286step1 raw23286step1Labels := by
      have ha : raw23286step1 = (fun i j => raw23286step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23286step1 raw23286step0; decide +kernel
      have hl : raw23286step1Labels = raw23286step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23286step0 raw23286step0Labels permutation38 permutation6
    _ = mixedMoment B node985 node985Labels := by rfl

def raw23287 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23287 raw23287Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw23287 raw23287Labels = mixedMoment B raw23287step0 raw23287step0Labels := by
      have hz : ∀ j, raw23287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23287step0 = (fun i j => raw23287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23287step0 raw23287; decide +kernel
      have hl : raw23287step0Labels = raw23287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23287 raw23287Labels permutation346 hz
    mixedMoment B raw23287step0 raw23287step0Labels = mixedMoment B raw23287step1 raw23287step1Labels := by
      have ha : raw23287step1 = (fun i j => raw23287step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23287step1 raw23287step0; decide +kernel
      have hl : raw23287step1Labels = raw23287step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23287step0 raw23287step0Labels permutation38 permutation6
    _ = mixedMoment B node985 node985Labels := by rfl

def raw23288 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23288 raw23288Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw23288 raw23288Labels = mixedMoment B raw23288step0 raw23288step0Labels := by
      have hz : ∀ j, raw23288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23288step0 = (fun i j => raw23288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23288step0 raw23288; decide +kernel
      have hl : raw23288step0Labels = raw23288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23288 raw23288Labels permutation434 hz
    mixedMoment B raw23288step0 raw23288step0Labels = mixedMoment B raw23288step1 raw23288step1Labels := by
      have ha : raw23288step1 = (fun i j => raw23288step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23288step1 raw23288step0; decide +kernel
      have hl : raw23288step1Labels = raw23288step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23288step0 raw23288step0Labels permutation32 permutation7
    mixedMoment B raw23288step1 raw23288step1Labels = mixedMoment B raw23288step2 raw23288step2Labels := by
      have ha : raw23288step2 = raw23288step1 := by apply Matrix.ext; unfold raw23288step2 raw23288step1; decide +kernel
      have hl : raw23288step1Labels = labelEmbedding1 ∘ raw23288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23288step1 raw23288step1Labels raw23288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw23289 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23289step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23289step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23289step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23289step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23289 raw23289Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw23289 raw23289Labels = mixedMoment B raw23289step0 raw23289step0Labels := by
      have hz : ∀ j, raw23289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23289step0 = (fun i j => raw23289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23289step0 raw23289; decide +kernel
      have hl : raw23289step0Labels = raw23289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23289 raw23289Labels permutation434 hz
    mixedMoment B raw23289step0 raw23289step0Labels = mixedMoment B raw23289step1 raw23289step1Labels := by
      have hz : ∀ j, raw23289step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23289step1 = (fun i j => raw23289step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23289step1 raw23289step0; decide +kernel
      have hl : raw23289step1Labels = raw23289step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23289step0 raw23289step0Labels permutation80 hz
    mixedMoment B raw23289step1 raw23289step1Labels = mixedMoment B raw23289step2 raw23289step2Labels := by
      have ha : raw23289step2 = (fun i j => raw23289step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23289step2 raw23289step1; decide +kernel
      have hl : raw23289step2Labels = raw23289step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23289step1 raw23289step1Labels permutation9 permutation7
    mixedMoment B raw23289step2 raw23289step2Labels = mixedMoment B raw23289step3 raw23289step3Labels := by
      have ha : raw23289step3 = raw23289step2 := by apply Matrix.ext; unfold raw23289step3 raw23289step2; decide +kernel
      have hl : raw23289step2Labels = labelEmbedding1 ∘ raw23289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23289step2 raw23289step2Labels raw23289step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw23290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23290step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw23290step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23290step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw23290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23290 raw23290Labels = mixedMoment B node1473 node1473Labels := by
  calc
    mixedMoment B raw23290 raw23290Labels = mixedMoment B raw23290step0 raw23290step0Labels := by
      have hz : ∀ j, raw23290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23290step0 = (fun i j => raw23290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23290step0 raw23290; decide +kernel
      have hl : raw23290step0Labels = raw23290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23290 raw23290Labels permutation434 hz
    mixedMoment B raw23290step0 raw23290step0Labels = mixedMoment B raw23290step1 raw23290step1Labels := by
      have hz : ∀ j, raw23290step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23290step1 = (fun i j => raw23290step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23290step1 raw23290step0; decide +kernel
      have hl : raw23290step1Labels = raw23290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23290step0 raw23290step0Labels permutation80 hz
    mixedMoment B raw23290step1 raw23290step1Labels = mixedMoment B raw23290step2 raw23290step2Labels := by
      have ha : raw23290step2 = (fun i j => raw23290step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23290step2 raw23290step1; decide +kernel
      have hl : raw23290step2Labels = raw23290step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23290step1 raw23290step1Labels permutation8 permutation7
    mixedMoment B raw23290step2 raw23290step2Labels = mixedMoment B raw23290step3 raw23290step3Labels := by
      have ha : raw23290step3 = raw23290step2 := by apply Matrix.ext; unfold raw23290step3 raw23290step2; decide +kernel
      have hl : raw23290step2Labels = labelEmbedding1 ∘ raw23290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23290step2 raw23290step2Labels raw23290step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1473 node1473Labels := by rfl

def raw23291 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23291 raw23291Labels = mixedMoment B node1363 node1363Labels := by
  calc
    mixedMoment B raw23291 raw23291Labels = mixedMoment B raw23291step0 raw23291step0Labels := by
      have hz : ∀ j, raw23291 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23291step0 = (fun i j => raw23291 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23291step0 raw23291; decide +kernel
      have hl : raw23291step0Labels = raw23291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23291 raw23291Labels permutation434 hz
    mixedMoment B raw23291step0 raw23291step0Labels = mixedMoment B raw23291step1 raw23291step1Labels := by
      have ha : raw23291step1 = (fun i j => raw23291step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23291step1 raw23291step0; decide +kernel
      have hl : raw23291step1Labels = raw23291step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23291step0 raw23291step0Labels permutation32 permutation7
    mixedMoment B raw23291step1 raw23291step1Labels = mixedMoment B raw23291step2 raw23291step2Labels := by
      have ha : raw23291step2 = raw23291step1 := by apply Matrix.ext; unfold raw23291step2 raw23291step1; decide +kernel
      have hl : raw23291step1Labels = labelEmbedding1 ∘ raw23291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23291step1 raw23291step1Labels raw23291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1363 node1363Labels := by rfl

def raw23292 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23292step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23292 raw23292Labels = mixedMoment B node1363 node1363Labels := by
  calc
    mixedMoment B raw23292 raw23292Labels = mixedMoment B raw23292step0 raw23292step0Labels := by
      have hz : ∀ j, raw23292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23292step0 = (fun i j => raw23292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23292step0 raw23292; decide +kernel
      have hl : raw23292step0Labels = raw23292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23292 raw23292Labels permutation346 hz
    mixedMoment B raw23292step0 raw23292step0Labels = mixedMoment B raw23292step1 raw23292step1Labels := by
      have ha : raw23292step1 = (fun i j => raw23292step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23292step1 raw23292step0; decide +kernel
      have hl : raw23292step1Labels = raw23292step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23292step0 raw23292step0Labels permutation32 permutation7
    mixedMoment B raw23292step1 raw23292step1Labels = mixedMoment B raw23292step2 raw23292step2Labels := by
      have ha : raw23292step2 = raw23292step1 := by apply Matrix.ext; unfold raw23292step2 raw23292step1; decide +kernel
      have hl : raw23292step1Labels = labelEmbedding1 ∘ raw23292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23292step1 raw23292step1Labels raw23292step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1363 node1363Labels := by rfl

def raw23293 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23293step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23293step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23293step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23293 raw23293Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw23293 raw23293Labels = mixedMoment B raw23293step0 raw23293step0Labels := by
      have hz : ∀ j, raw23293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23293step0 = (fun i j => raw23293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23293step0 raw23293; decide +kernel
      have hl : raw23293step0Labels = raw23293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23293 raw23293Labels permutation434 hz
    mixedMoment B raw23293step0 raw23293step0Labels = mixedMoment B raw23293step1 raw23293step1Labels := by
      have hz : ∀ j, raw23293step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23293step1 = (fun i j => raw23293step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23293step1 raw23293step0; decide +kernel
      have hl : raw23293step1Labels = raw23293step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23293step0 raw23293step0Labels permutation80 hz
    mixedMoment B raw23293step1 raw23293step1Labels = mixedMoment B raw23293step2 raw23293step2Labels := by
      have ha : raw23293step2 = (fun i j => raw23293step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23293step2 raw23293step1; decide +kernel
      have hl : raw23293step2Labels = raw23293step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23293step1 raw23293step1Labels permutation9 permutation7
    mixedMoment B raw23293step2 raw23293step2Labels = mixedMoment B raw23293step3 raw23293step3Labels := by
      have ha : raw23293step3 = raw23293step2 := by apply Matrix.ext; unfold raw23293step3 raw23293step2; decide +kernel
      have hl : raw23293step2Labels = labelEmbedding1 ∘ raw23293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23293step2 raw23293step2Labels raw23293step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1375 node1375Labels := by rfl

def raw23294 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23294step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23294 raw23294Labels = mixedMoment B node1479 node1479Labels := by
  calc
    mixedMoment B raw23294 raw23294Labels = mixedMoment B raw23294step0 raw23294step0Labels := by
      have hz : ∀ j, raw23294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23294step0 = (fun i j => raw23294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23294step0 raw23294; decide +kernel
      have hl : raw23294step0Labels = raw23294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23294 raw23294Labels permutation434 hz
    mixedMoment B raw23294step0 raw23294step0Labels = mixedMoment B raw23294step1 raw23294step1Labels := by
      have ha : raw23294step1 = (fun i j => raw23294step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23294step1 raw23294step0; decide +kernel
      have hl : raw23294step1Labels = raw23294step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23294step0 raw23294step0Labels permutation32 permutation7
    mixedMoment B raw23294step1 raw23294step1Labels = mixedMoment B raw23294step2 raw23294step2Labels := by
      have ha : raw23294step2 = raw23294step1 := by apply Matrix.ext; unfold raw23294step2 raw23294step1; decide +kernel
      have hl : raw23294step1Labels = labelEmbedding1 ∘ raw23294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23294step1 raw23294step1Labels raw23294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1479 node1479Labels := by rfl

def raw23295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23295step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23295step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23295step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23295step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23295 raw23295Labels = mixedMoment B node1420 node1420Labels := by
  calc
    mixedMoment B raw23295 raw23295Labels = mixedMoment B raw23295step0 raw23295step0Labels := by
      have hz : ∀ j, raw23295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23295step0 = (fun i j => raw23295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23295step0 raw23295; decide +kernel
      have hl : raw23295step0Labels = raw23295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23295 raw23295Labels permutation434 hz
    mixedMoment B raw23295step0 raw23295step0Labels = mixedMoment B raw23295step1 raw23295step1Labels := by
      have hz : ∀ j, raw23295step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23295step1 = (fun i j => raw23295step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23295step1 raw23295step0; decide +kernel
      have hl : raw23295step1Labels = raw23295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23295step0 raw23295step0Labels permutation56 hz
    mixedMoment B raw23295step1 raw23295step1Labels = mixedMoment B raw23295step2 raw23295step2Labels := by
      have ha : raw23295step2 = (fun i j => raw23295step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23295step2 raw23295step1; decide +kernel
      have hl : raw23295step2Labels = raw23295step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23295step1 raw23295step1Labels permutation8 permutation7
    mixedMoment B raw23295step2 raw23295step2Labels = mixedMoment B raw23295step3 raw23295step3Labels := by
      have ha : raw23295step3 = raw23295step2 := by apply Matrix.ext; unfold raw23295step3 raw23295step2; decide +kernel
      have hl : raw23295step2Labels = labelEmbedding1 ∘ raw23295step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23295step2 raw23295step2Labels raw23295step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1420 node1420Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
