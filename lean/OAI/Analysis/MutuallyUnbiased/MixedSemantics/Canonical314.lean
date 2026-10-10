import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40192Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40192step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40192 raw40192Labels = mixedMoment B node8 node8Labels := by
  calc
    mixedMoment B raw40192 raw40192Labels = mixedMoment B raw40192step0 raw40192step0Labels := by
      have ha : raw40192step0 = (fun i j => raw40192 (permutation665 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40192step0 raw40192; decide +kernel
      have hl : raw40192step0Labels = raw40192Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40192 raw40192Labels permutation665 permutation6
    _ = mixedMoment B node8 node8Labels := by rfl

def raw40193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw40193Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40193step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40193 raw40193Labels = mixedMoment B node172 node172Labels := by
  calc
    mixedMoment B raw40193 raw40193Labels = mixedMoment B raw40193step0 raw40193step0Labels := by
      have ha : raw40193step0 = (fun i j => raw40193 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40193step0 raw40193; decide +kernel
      have hl : raw40193step0Labels = raw40193Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40193 raw40193Labels permutation506 permutation6
    _ = mixedMoment B node172 node172Labels := by rfl

def raw40194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40194Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40194step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40194 raw40194Labels = mixedMoment B node321 node321Labels := by
  calc
    mixedMoment B raw40194 raw40194Labels = mixedMoment B raw40194step0 raw40194step0Labels := by
      have ha : raw40194step0 = (fun i j => raw40194 (permutation659 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40194step0 raw40194; decide +kernel
      have hl : raw40194step0Labels = raw40194Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40194 raw40194Labels permutation659 permutation7
    _ = mixedMoment B node321 node321Labels := by rfl

def raw40195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40195Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw40195step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40195step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40195 raw40195Labels = mixedMoment B node24 node24Labels := by
  calc
    mixedMoment B raw40195 raw40195Labels = mixedMoment B raw40195step0 raw40195step0Labels := by
      have hz : ∀ j, raw40195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40195step0 = (fun i j => raw40195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40195step0 raw40195; decide +kernel
      have hl : raw40195step0Labels = raw40195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40195 raw40195Labels permutation434 hz
    mixedMoment B raw40195step0 raw40195step0Labels = mixedMoment B raw40195step1 raw40195step1Labels := by
      have ha : raw40195step1 = (fun i j => raw40195step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40195step1 raw40195step0; decide +kernel
      have hl : raw40195step1Labels = raw40195step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40195step0 raw40195step0Labels permutation129 permutation6
    _ = mixedMoment B node24 node24Labels := by rfl

def raw40196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw40196Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw40196step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40196 raw40196Labels = mixedMoment B node163 node163Labels := by
  calc
    mixedMoment B raw40196 raw40196Labels = mixedMoment B raw40196step0 raw40196step0Labels := by
      have ha : raw40196step0 = (fun i j => raw40196 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40196step0 raw40196; decide +kernel
      have hl : raw40196step0Labels = raw40196Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40196 raw40196Labels permutation514 permutation6
    _ = mixedMoment B node163 node163Labels := by rfl

def raw40197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40197Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw40197step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw40197step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40197 raw40197Labels = mixedMoment B node9 node9Labels := by
  calc
    mixedMoment B raw40197 raw40197Labels = mixedMoment B raw40197step0 raw40197step0Labels := by
      have hz : ∀ j, raw40197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40197step0 = (fun i j => raw40197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40197step0 raw40197; decide +kernel
      have hl : raw40197step0Labels = raw40197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40197 raw40197Labels permutation434 hz
    mixedMoment B raw40197step0 raw40197step0Labels = mixedMoment B raw40197step1 raw40197step1Labels := by
      have ha : raw40197step1 = (fun i j => raw40197step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40197step1 raw40197step0; decide +kernel
      have hl : raw40197step1Labels = raw40197step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40197step0 raw40197step0Labels permutation146 permutation6
    _ = mixedMoment B node9 node9Labels := by rfl

def raw40198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40198Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40198step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40198step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40198step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40198 raw40198Labels = mixedMoment B node260 node260Labels := by
  calc
    mixedMoment B raw40198 raw40198Labels = mixedMoment B raw40198step0 raw40198step0Labels := by
      have hz : ∀ j, raw40198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40198step0 = (fun i j => raw40198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40198step0 raw40198; decide +kernel
      have hl : raw40198step0Labels = raw40198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40198 raw40198Labels permutation434 hz
    mixedMoment B raw40198step0 raw40198step0Labels = mixedMoment B raw40198step1 raw40198step1Labels := by
      have ha : raw40198step1 = (fun i j => raw40198step0 (permutation80 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40198step1 raw40198step0; decide +kernel
      have hl : raw40198step1Labels = raw40198step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40198step0 raw40198step0Labels permutation80 permutation4
    mixedMoment B raw40198step1 raw40198step1Labels = mixedMoment B raw40198step2 raw40198step2Labels := by
      have ha : raw40198step2 = -raw40198step1 := by apply Matrix.ext; change ∀ i j, raw40198step2 i j = -(raw40198step1 i j); unfold raw40198step2 raw40198step1; decide +kernel
      have hl : raw40198step2Labels = raw40198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node260 node260Labels := by rfl

def raw40199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40199Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40199step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40199 raw40199Labels = mixedMoment B node243 node243Labels := by
  calc
    mixedMoment B raw40199 raw40199Labels = mixedMoment B raw40199step0 raw40199step0Labels := by
      have ha : raw40199step0 = (fun i j => raw40199 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40199step0 raw40199; decide +kernel
      have hl : raw40199step0Labels = raw40199Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40199 raw40199Labels permutation414 permutation6
    _ = mixedMoment B node243 node243Labels := by rfl

def raw40200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40200Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40200step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40200 raw40200Labels = mixedMoment B node171 node171Labels := by
  calc
    mixedMoment B raw40200 raw40200Labels = mixedMoment B raw40200step0 raw40200step0Labels := by
      have ha : raw40200step0 = (fun i j => raw40200 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40200step0 raw40200; decide +kernel
      have hl : raw40200step0Labels = raw40200Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40200 raw40200Labels permutation414 permutation6
    _ = mixedMoment B node171 node171Labels := by rfl

def raw40201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40201Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40201step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40201 raw40201Labels = mixedMoment B node232 node232Labels := by
  calc
    mixedMoment B raw40201 raw40201Labels = mixedMoment B raw40201step0 raw40201step0Labels := by
      have ha : raw40201step0 = (fun i j => raw40201 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40201step0 raw40201; decide +kernel
      have hl : raw40201step0Labels = raw40201Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40201 raw40201Labels permutation399 permutation6
    _ = mixedMoment B node232 node232Labels := by rfl

def raw40202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40202Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40202step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40202step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40202 raw40202Labels = mixedMoment B node259 node259Labels := by
  calc
    mixedMoment B raw40202 raw40202Labels = mixedMoment B raw40202step0 raw40202step0Labels := by
      have ha : raw40202step0 = (fun i j => raw40202 (permutation349 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40202step0 raw40202; decide +kernel
      have hl : raw40202step0Labels = raw40202Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40202 raw40202Labels permutation349 permutation4
    mixedMoment B raw40202step0 raw40202step0Labels = mixedMoment B raw40202step1 raw40202step1Labels := by
      have ha : raw40202step1 = -raw40202step0 := by apply Matrix.ext; change ∀ i j, raw40202step1 i j = -(raw40202step0 i j); unfold raw40202step1 raw40202step0; decide +kernel
      have hl : raw40202step1Labels = raw40202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node259 node259Labels := by rfl

def raw40203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40203Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40203step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40203 raw40203Labels = mixedMoment B node220 node220Labels := by
  calc
    mixedMoment B raw40203 raw40203Labels = mixedMoment B raw40203step0 raw40203step0Labels := by
      have ha : raw40203step0 = (fun i j => raw40203 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40203step0 raw40203; decide +kernel
      have hl : raw40203step0Labels = raw40203Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40203 raw40203Labels permutation409 permutation6
    _ = mixedMoment B node220 node220Labels := by rfl

def raw40204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40204Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw40204step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0]]
def raw40204step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40204step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw40204step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40204step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40204step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40204 raw40204Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw40204 raw40204Labels = mixedMoment B raw40204step0 raw40204step0Labels := by
      have hz : ∀ j, raw40204 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40204step0 = (fun i j => raw40204 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40204step0 raw40204; decide +kernel
      have hl : raw40204step0Labels = raw40204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40204 raw40204Labels permutation520 hz
    mixedMoment B raw40204step0 raw40204step0Labels = mixedMoment B raw40204step1 raw40204step1Labels := by
      have hz : ∀ j, raw40204step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40204step1 = (fun i j => raw40204step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40204step1 raw40204step0; decide +kernel
      have hl : raw40204step1Labels = raw40204step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40204step0 raw40204step0Labels permutation104 hz
    mixedMoment B raw40204step1 raw40204step1Labels = mixedMoment B raw40204step2 raw40204step2Labels := by
      have ha : raw40204step2 = (fun i j => raw40204step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40204step2 raw40204step1; decide +kernel
      have hl : raw40204step2Labels = raw40204step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40204step1 raw40204step1Labels permutation20 permutation4
    mixedMoment B raw40204step2 raw40204step2Labels = mixedMoment B raw40204step3 raw40204step3Labels := by
      have ha : raw40204step3 = -raw40204step2 := by apply Matrix.ext; change ∀ i j, raw40204step3 i j = -(raw40204step2 i j); unfold raw40204step3 raw40204step2; decide +kernel
      have hl : raw40204step3Labels = raw40204step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node505 node505Labels := by rfl

def raw40205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40205Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw40205step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40205step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40205 raw40205Labels = mixedMoment B node502 node502Labels := by
  calc
    mixedMoment B raw40205 raw40205Labels = mixedMoment B raw40205step0 raw40205step0Labels := by
      have hz : ∀ j, raw40205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40205step0 = (fun i j => raw40205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40205step0 raw40205; decide +kernel
      have hl : raw40205step0Labels = raw40205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40205 raw40205Labels permutation434 hz
    mixedMoment B raw40205step0 raw40205step0Labels = mixedMoment B raw40205step1 raw40205step1Labels := by
      have ha : raw40205step1 = (fun i j => raw40205step0 (permutation98 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40205step1 raw40205step0; decide +kernel
      have hl : raw40205step1Labels = raw40205step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40205step0 raw40205step0Labels permutation98 permutation6
    _ = mixedMoment B node502 node502Labels := by rfl

def raw40206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40206Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]
def raw40206step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40206step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40206 raw40206Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw40206 raw40206Labels = mixedMoment B raw40206step0 raw40206step0Labels := by
      have hz : ∀ j, raw40206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40206step0 = (fun i j => raw40206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40206step0 raw40206; decide +kernel
      have hl : raw40206step0Labels = raw40206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40206 raw40206Labels permutation434 hz
    mixedMoment B raw40206step0 raw40206step0Labels = mixedMoment B raw40206step1 raw40206step1Labels := by
      have ha : raw40206step1 = (fun i j => raw40206step0 (permutation98 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40206step1 raw40206step0; decide +kernel
      have hl : raw40206step1Labels = raw40206step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40206step0 raw40206step0Labels permutation98 permutation6
    _ = mixedMoment B node449 node449Labels := by rfl

def raw40207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40207Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40207step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40207 raw40207Labels = mixedMoment B node448 node448Labels := by
  calc
    mixedMoment B raw40207 raw40207Labels = mixedMoment B raw40207step0 raw40207step0Labels := by
      have ha : raw40207step0 = (fun i j => raw40207 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40207step0 raw40207; decide +kernel
      have hl : raw40207step0Labels = raw40207Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40207 raw40207Labels permutation414 permutation6
    _ = mixedMoment B node448 node448Labels := by rfl

def raw40208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40208Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40208step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40208 raw40208Labels = mixedMoment B node436 node436Labels := by
  calc
    mixedMoment B raw40208 raw40208Labels = mixedMoment B raw40208step0 raw40208step0Labels := by
      have ha : raw40208step0 = (fun i j => raw40208 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40208step0 raw40208; decide +kernel
      have hl : raw40208step0Labels = raw40208Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40208 raw40208Labels permutation399 permutation6
    _ = mixedMoment B node436 node436Labels := by rfl

def raw40209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40209Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40209step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40209 raw40209Labels = mixedMoment B node429 node429Labels := by
  calc
    mixedMoment B raw40209 raw40209Labels = mixedMoment B raw40209step0 raw40209step0Labels := by
      have ha : raw40209step0 = (fun i j => raw40209 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40209step0 raw40209; decide +kernel
      have hl : raw40209step0Labels = raw40209Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40209 raw40209Labels permutation409 permutation6
    _ = mixedMoment B node429 node429Labels := by rfl

def raw40210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw40210Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40210step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw40210step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40210step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40210 raw40210Labels = mixedMoment B node504 node504Labels := by
  calc
    mixedMoment B raw40210 raw40210Labels = mixedMoment B raw40210step0 raw40210step0Labels := by
      have hz : ∀ j, raw40210 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40210step0 = (fun i j => raw40210 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40210step0 raw40210; decide +kernel
      have hl : raw40210step0Labels = raw40210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40210 raw40210Labels permutation520 hz
    mixedMoment B raw40210step0 raw40210step0Labels = mixedMoment B raw40210step1 raw40210step1Labels := by
      have ha : raw40210step1 = (fun i j => raw40210step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40210step1 raw40210step0; decide +kernel
      have hl : raw40210step1Labels = raw40210step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40210step0 raw40210step0Labels permutation144 permutation3
    mixedMoment B raw40210step1 raw40210step1Labels = mixedMoment B raw40210step2 raw40210step2Labels := by
      have ha : raw40210step2 = -raw40210step1 := by apply Matrix.ext; change ∀ i j, raw40210step2 i j = -(raw40210step1 i j); unfold raw40210step2 raw40210step1; decide +kernel
      have hl : raw40210step2Labels = raw40210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node504 node504Labels := by rfl

def raw40211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw40211Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40211step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40211step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40211 raw40211Labels = mixedMoment B node525 node525Labels := by
  calc
    mixedMoment B raw40211 raw40211Labels = mixedMoment B raw40211step0 raw40211step0Labels := by
      have ha : raw40211step0 = (fun i j => raw40211 (permutation639 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40211step0 raw40211; decide +kernel
      have hl : raw40211step0Labels = raw40211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40211 raw40211Labels permutation639 permutation2
    mixedMoment B raw40211step0 raw40211step0Labels = mixedMoment B raw40211step1 raw40211step1Labels := by
      have ha : raw40211step1 = -raw40211step0 := by apply Matrix.ext; change ∀ i j, raw40211step1 i j = -(raw40211step0 i j); unfold raw40211step1 raw40211step0; decide +kernel
      have hl : raw40211step1Labels = raw40211step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node525 node525Labels := by rfl

def raw40212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw40212Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40212step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40212step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40212 raw40212Labels = mixedMoment B node207 node207Labels := by
  calc
    mixedMoment B raw40212 raw40212Labels = mixedMoment B raw40212step0 raw40212step0Labels := by
      have ha : raw40212step0 = (fun i j => raw40212 (permutation520 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40212step0 raw40212; decide +kernel
      have hl : raw40212step0Labels = raw40212Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40212 raw40212Labels permutation520 permutation6
    mixedMoment B raw40212step0 raw40212step0Labels = mixedMoment B raw40212step1 raw40212step1Labels := by
      have ha : raw40212step1 = -raw40212step0 := by apply Matrix.ext; change ∀ i j, raw40212step1 i j = -(raw40212step0 i j); unfold raw40212step1 raw40212step0; decide +kernel
      have hl : raw40212step1Labels = raw40212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node207 node207Labels := by rfl

def raw40213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2]]
def raw40213Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw40213step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40213 raw40213Labels = mixedMoment B node371 node371Labels := by
  calc
    mixedMoment B raw40213 raw40213Labels = mixedMoment B raw40213step0 raw40213step0Labels := by
      have ha : raw40213step0 = (fun i j => raw40213 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40213step0 raw40213; decide +kernel
      have hl : raw40213step0Labels = raw40213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40213 raw40213Labels permutation590 permutation4
    _ = mixedMoment B node371 node371Labels := by rfl

def raw40214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40214Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw40214step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40214step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40214 raw40214Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw40214 raw40214Labels = mixedMoment B raw40214step0 raw40214step0Labels := by
      have hz : ∀ j, raw40214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40214step0 = (fun i j => raw40214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40214step0 raw40214; decide +kernel
      have hl : raw40214step0Labels = raw40214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40214 raw40214Labels permutation434 hz
    mixedMoment B raw40214step0 raw40214step0Labels = mixedMoment B raw40214step1 raw40214step1Labels := by
      have ha : raw40214step1 = (fun i j => raw40214step0 (permutation140 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40214step1 raw40214step0; decide +kernel
      have hl : raw40214step1Labels = raw40214step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40214step0 raw40214step0Labels permutation140 permutation7
    _ = mixedMoment B node339 node339Labels := by rfl

def raw40215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw40215Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40215step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40215 raw40215Labels = mixedMoment B node334 node334Labels := by
  calc
    mixedMoment B raw40215 raw40215Labels = mixedMoment B raw40215step0 raw40215step0Labels := by
      have ha : raw40215step0 = (fun i j => raw40215 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40215step0 raw40215; decide +kernel
      have hl : raw40215step0Labels = raw40215Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40215 raw40215Labels permutation639 permutation7
    _ = mixedMoment B node334 node334Labels := by rfl

def raw40216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40216Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40216step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40216 raw40216Labels = mixedMoment B node310 node310Labels := by
  calc
    mixedMoment B raw40216 raw40216Labels = mixedMoment B raw40216step0 raw40216step0Labels := by
      have ha : raw40216step0 = (fun i j => raw40216 (permutation541 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40216step0 raw40216; decide +kernel
      have hl : raw40216step0Labels = raw40216Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40216 raw40216Labels permutation541 permutation6
    _ = mixedMoment B node310 node310Labels := by rfl

def raw40217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40217Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40217step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40217 raw40217Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40217 raw40217Labels = mixedMoment B raw40217step0 raw40217step0Labels := by
      have ha : raw40217step0 = (fun i j => raw40217 (permutation547 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40217step0 raw40217; decide +kernel
      have hl : raw40217step0Labels = raw40217Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40217 raw40217Labels permutation547 permutation6
    _ = mixedMoment B node520 node520Labels := by rfl

def raw40218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40218Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40218step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40218 raw40218Labels = mixedMoment B node301 node301Labels := by
  calc
    mixedMoment B raw40218 raw40218Labels = mixedMoment B raw40218step0 raw40218step0Labels := by
      have ha : raw40218step0 = (fun i j => raw40218 (permutation547 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40218step0 raw40218; decide +kernel
      have hl : raw40218step0Labels = raw40218Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40218 raw40218Labels permutation547 permutation6
    _ = mixedMoment B node301 node301Labels := by rfl

def raw40219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw40219Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw40219step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40219step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40219 raw40219Labels = mixedMoment B node155 node155Labels := by
  calc
    mixedMoment B raw40219 raw40219Labels = mixedMoment B raw40219step0 raw40219step0Labels := by
      have hz : ∀ j, raw40219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40219step0 = (fun i j => raw40219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40219step0 raw40219; decide +kernel
      have hl : raw40219step0Labels = raw40219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40219 raw40219Labels permutation346 hz
    mixedMoment B raw40219step0 raw40219step0Labels = mixedMoment B raw40219step1 raw40219step1Labels := by
      have ha : raw40219step1 = (fun i j => raw40219step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40219step1 raw40219step0; decide +kernel
      have hl : raw40219step1Labels = raw40219step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40219step0 raw40219step0Labels permutation128 permutation6
    _ = mixedMoment B node155 node155Labels := by rfl

def raw40220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw40220Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40220step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40220 raw40220Labels = mixedMoment B node22 node22Labels := by
  calc
    mixedMoment B raw40220 raw40220Labels = mixedMoment B raw40220step0 raw40220step0Labels := by
      have ha : raw40220step0 = (fun i j => raw40220 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40220step0 raw40220; decide +kernel
      have hl : raw40220step0Labels = raw40220Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40220 raw40220Labels permutation590 permutation6
    _ = mixedMoment B node22 node22Labels := by rfl

def raw40221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40221Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40221step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40221 raw40221Labels = mixedMoment B node91 node91Labels := by
  calc
    mixedMoment B raw40221 raw40221Labels = mixedMoment B raw40221step0 raw40221step0Labels := by
      have ha : raw40221step0 = (fun i j => raw40221 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40221step0 raw40221; decide +kernel
      have hl : raw40221step0Labels = raw40221Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40221 raw40221Labels permutation569 permutation6
    _ = mixedMoment B node91 node91Labels := by rfl

def raw40222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40222Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![2, -2, 0]]
def raw40222step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![2, -2, 0]]
def raw40222step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40222step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40222step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40222step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40222step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40222 raw40222Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw40222 raw40222Labels = mixedMoment B raw40222step0 raw40222step0Labels := by
      have hz : ∀ j, raw40222 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40222step0 = (fun i j => raw40222 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40222step0 raw40222; decide +kernel
      have hl : raw40222step0Labels = raw40222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40222 raw40222Labels permutation520 hz
    mixedMoment B raw40222step0 raw40222step0Labels = mixedMoment B raw40222step1 raw40222step1Labels := by
      have hz : ∀ j, raw40222step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40222step1 = (fun i j => raw40222step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40222step1 raw40222step0; decide +kernel
      have hl : raw40222step1Labels = raw40222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40222step0 raw40222step0Labels permutation104 hz
    mixedMoment B raw40222step1 raw40222step1Labels = mixedMoment B raw40222step2 raw40222step2Labels := by
      have ha : raw40222step2 = (fun i j => raw40222step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40222step2 raw40222step1; decide +kernel
      have hl : raw40222step2Labels = raw40222step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40222step1 raw40222step1Labels permutation20 permutation4
    mixedMoment B raw40222step2 raw40222step2Labels = mixedMoment B raw40222step3 raw40222step3Labels := by
      have ha : raw40222step3 = -raw40222step2 := by apply Matrix.ext; change ∀ i j, raw40222step3 i j = -(raw40222step2 i j); unfold raw40222step3 raw40222step2; decide +kernel
      have hl : raw40222step3Labels = raw40222step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node268 node268Labels := by rfl

def raw40223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40223Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![2, -1, -1]]
def raw40223step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40223step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40223 raw40223Labels = mixedMoment B node245 node245Labels := by
  calc
    mixedMoment B raw40223 raw40223Labels = mixedMoment B raw40223step0 raw40223step0Labels := by
      have hz : ∀ j, raw40223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40223step0 = (fun i j => raw40223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40223step0 raw40223; decide +kernel
      have hl : raw40223step0Labels = raw40223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40223 raw40223Labels permutation434 hz
    mixedMoment B raw40223step0 raw40223step0Labels = mixedMoment B raw40223step1 raw40223step1Labels := by
      have ha : raw40223step1 = (fun i j => raw40223step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40223step1 raw40223step0; decide +kernel
      have hl : raw40223step1Labels = raw40223step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40223step0 raw40223step0Labels permutation99 permutation6
    _ = mixedMoment B node245 node245Labels := by rfl

def raw40224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40224Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -2, 2], ![2, 0, -2]]
def raw40224step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40224step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40224 raw40224Labels = mixedMoment B node178 node178Labels := by
  calc
    mixedMoment B raw40224 raw40224Labels = mixedMoment B raw40224step0 raw40224step0Labels := by
      have hz : ∀ j, raw40224 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40224step0 = (fun i j => raw40224 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40224step0 raw40224; decide +kernel
      have hl : raw40224step0Labels = raw40224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40224 raw40224Labels permutation434 hz
    mixedMoment B raw40224step0 raw40224step0Labels = mixedMoment B raw40224step1 raw40224step1Labels := by
      have ha : raw40224step1 = (fun i j => raw40224step0 (permutation98 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40224step1 raw40224step0; decide +kernel
      have hl : raw40224step1Labels = raw40224step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40224step0 raw40224step0Labels permutation98 permutation6
    _ = mixedMoment B node178 node178Labels := by rfl

def raw40225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw40225Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40225step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40225step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40225 raw40225Labels = mixedMoment B node234 node234Labels := by
  calc
    mixedMoment B raw40225 raw40225Labels = mixedMoment B raw40225step0 raw40225step0Labels := by
      have hz : ∀ j, raw40225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40225step0 = (fun i j => raw40225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40225step0 raw40225; decide +kernel
      have hl : raw40225step0Labels = raw40225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40225 raw40225Labels permutation434 hz
    mixedMoment B raw40225step0 raw40225step0Labels = mixedMoment B raw40225step1 raw40225step1Labels := by
      have ha : raw40225step1 = (fun i j => raw40225step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40225step1 raw40225step0; decide +kernel
      have hl : raw40225step1Labels = raw40225step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40225step0 raw40225step0Labels permutation93 permutation6
    _ = mixedMoment B node234 node234Labels := by rfl

def raw40226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40226Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40226step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40226step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40226 raw40226Labels = mixedMoment B node260 node260Labels := by
  calc
    mixedMoment B raw40226 raw40226Labels = mixedMoment B raw40226step0 raw40226step0Labels := by
      have hz : ∀ j, raw40226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40226step0 = (fun i j => raw40226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40226step0 raw40226; decide +kernel
      have hl : raw40226step0Labels = raw40226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40226 raw40226Labels permutation434 hz
    mixedMoment B raw40226step0 raw40226step0Labels = mixedMoment B raw40226step1 raw40226step1Labels := by
      have ha : raw40226step1 = (fun i j => raw40226step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40226step1 raw40226step0; decide +kernel
      have hl : raw40226step1Labels = raw40226step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40226step0 raw40226step0Labels permutation96 permutation6
    _ = mixedMoment B node260 node260Labels := by rfl

def raw40227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40227Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40227step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40227 raw40227Labels = mixedMoment B node174 node174Labels := by
  calc
    mixedMoment B raw40227 raw40227Labels = mixedMoment B raw40227step0 raw40227step0Labels := by
      have ha : raw40227step0 = (fun i j => raw40227 (permutation416 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40227step0 raw40227; decide +kernel
      have hl : raw40227step0Labels = raw40227Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40227 raw40227Labels permutation416 permutation6
    _ = mixedMoment B node174 node174Labels := by rfl

def raw40228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40228Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40228step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40228 raw40228Labels = mixedMoment B node221 node221Labels := by
  calc
    mixedMoment B raw40228 raw40228Labels = mixedMoment B raw40228step0 raw40228step0Labels := by
      have ha : raw40228step0 = (fun i j => raw40228 (permutation410 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40228step0 raw40228; decide +kernel
      have hl : raw40228step0Labels = raw40228Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40228 raw40228Labels permutation410 permutation6
    _ = mixedMoment B node221 node221Labels := by rfl

def raw40229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw40229Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw40229step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40229step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40229step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40229 raw40229Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw40229 raw40229Labels = mixedMoment B raw40229step0 raw40229step0Labels := by
      have hz : ∀ j, raw40229 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40229step0 = (fun i j => raw40229 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40229step0 raw40229; decide +kernel
      have hl : raw40229step0Labels = raw40229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40229 raw40229Labels permutation520 hz
    mixedMoment B raw40229step0 raw40229step0Labels = mixedMoment B raw40229step1 raw40229step1Labels := by
      have ha : raw40229step1 = (fun i j => raw40229step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40229step1 raw40229step0; decide +kernel
      have hl : raw40229step1Labels = raw40229step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40229step0 raw40229step0Labels permutation92 permutation4
    mixedMoment B raw40229step1 raw40229step1Labels = mixedMoment B raw40229step2 raw40229step2Labels := by
      have ha : raw40229step2 = -raw40229step1 := by apply Matrix.ext; change ∀ i j, raw40229step2 i j = -(raw40229step1 i j); unfold raw40229step2 raw40229step1; decide +kernel
      have hl : raw40229step2Labels = raw40229step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node467 node467Labels := by rfl

def raw40230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw40230Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40230step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40230step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40230 raw40230Labels = mixedMoment B node424 node424Labels := by
  calc
    mixedMoment B raw40230 raw40230Labels = mixedMoment B raw40230step0 raw40230step0Labels := by
      have ha : raw40230step0 = (fun i j => raw40230 (permutation530 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40230step0 raw40230; decide +kernel
      have hl : raw40230step0Labels = raw40230Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40230 raw40230Labels permutation530 permutation6
    mixedMoment B raw40230step0 raw40230step0Labels = mixedMoment B raw40230step1 raw40230step1Labels := by
      have ha : raw40230step1 = -raw40230step0 := by apply Matrix.ext; change ∀ i j, raw40230step1 i j = -(raw40230step0 i j); unfold raw40230step1 raw40230step0; decide +kernel
      have hl : raw40230step1Labels = raw40230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node424 node424Labels := by rfl

def raw40231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40231Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw40231step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1]]
def raw40231step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40231step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40231 raw40231Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw40231 raw40231Labels = mixedMoment B raw40231step0 raw40231step0Labels := by
      have hz : ∀ j, raw40231 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40231step0 = (fun i j => raw40231 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40231step0 raw40231; decide +kernel
      have hl : raw40231step0Labels = raw40231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40231 raw40231Labels permutation520 hz
    mixedMoment B raw40231step0 raw40231step0Labels = mixedMoment B raw40231step1 raw40231step1Labels := by
      have hz : ∀ j, raw40231step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40231step1 = (fun i j => raw40231step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40231step1 raw40231step0; decide +kernel
      have hl : raw40231step1Labels = raw40231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40231step0 raw40231step0Labels permutation104 hz
    mixedMoment B raw40231step1 raw40231step1Labels = mixedMoment B raw40231step2 raw40231step2Labels := by
      have ha : raw40231step2 = (fun i j => raw40231step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40231step2 raw40231step1; decide +kernel
      have hl : raw40231step2Labels = raw40231step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40231step1 raw40231step1Labels permutation24 permutation6
    _ = mixedMoment B node503 node503Labels := by rfl

def raw40232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40232Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2]]
def raw40232step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40232step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40232 raw40232Labels = mixedMoment B node450 node450Labels := by
  calc
    mixedMoment B raw40232 raw40232Labels = mixedMoment B raw40232step0 raw40232step0Labels := by
      have hz : ∀ j, raw40232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40232step0 = (fun i j => raw40232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40232step0 raw40232; decide +kernel
      have hl : raw40232step0Labels = raw40232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40232 raw40232Labels permutation434 hz
    mixedMoment B raw40232step0 raw40232step0Labels = mixedMoment B raw40232step1 raw40232step1Labels := by
      have ha : raw40232step1 = (fun i j => raw40232step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40232step1 raw40232step0; decide +kernel
      have hl : raw40232step1Labels = raw40232step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40232step0 raw40232step0Labels permutation99 permutation6
    _ = mixedMoment B node450 node450Labels := by rfl

def raw40233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40233Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]
def raw40233step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40233step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40233 raw40233Labels = mixedMoment B node289 node289Labels := by
  calc
    mixedMoment B raw40233 raw40233Labels = mixedMoment B raw40233step0 raw40233step0Labels := by
      have hz : ∀ j, raw40233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40233step0 = (fun i j => raw40233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40233step0 raw40233; decide +kernel
      have hl : raw40233step0Labels = raw40233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40233 raw40233Labels permutation434 hz
    mixedMoment B raw40233step0 raw40233step0Labels = mixedMoment B raw40233step1 raw40233step1Labels := by
      have ha : raw40233step1 = (fun i j => raw40233step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40233step1 raw40233step0; decide +kernel
      have hl : raw40233step1Labels = raw40233step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40233step0 raw40233step0Labels permutation141 permutation7
    _ = mixedMoment B node289 node289Labels := by rfl

def raw40234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw40234Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40234step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40234step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40234 raw40234Labels = mixedMoment B node437 node437Labels := by
  calc
    mixedMoment B raw40234 raw40234Labels = mixedMoment B raw40234step0 raw40234step0Labels := by
      have hz : ∀ j, raw40234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40234step0 = (fun i j => raw40234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40234step0 raw40234; decide +kernel
      have hl : raw40234step0Labels = raw40234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40234 raw40234Labels permutation434 hz
    mixedMoment B raw40234step0 raw40234step0Labels = mixedMoment B raw40234step1 raw40234step1Labels := by
      have ha : raw40234step1 = (fun i j => raw40234step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40234step1 raw40234step0; decide +kernel
      have hl : raw40234step1Labels = raw40234step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40234step0 raw40234step0Labels permutation93 permutation6
    _ = mixedMoment B node437 node437Labels := by rfl

def raw40235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40235Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40235step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40235 raw40235Labels = mixedMoment B node423 node423Labels := by
  calc
    mixedMoment B raw40235 raw40235Labels = mixedMoment B raw40235step0 raw40235step0Labels := by
      have ha : raw40235step0 = (fun i j => raw40235 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40235step0 raw40235; decide +kernel
      have hl : raw40235step0Labels = raw40235Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40235 raw40235Labels permutation409 permutation6
    _ = mixedMoment B node423 node423Labels := by rfl

def raw40236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw40236Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40236step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40236 raw40236Labels = mixedMoment B node472 node472Labels := by
  calc
    mixedMoment B raw40236 raw40236Labels = mixedMoment B raw40236step0 raw40236step0Labels := by
      have ha : raw40236step0 = (fun i j => raw40236 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40236step0 raw40236; decide +kernel
      have hl : raw40236step0Labels = raw40236Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40236 raw40236Labels permutation639 permutation7
    _ = mixedMoment B node472 node472Labels := by rfl

def raw40237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40237Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40237step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40237step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40237 raw40237Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40237 raw40237Labels = mixedMoment B raw40237step0 raw40237step0Labels := by
      have ha : raw40237step0 = (fun i j => raw40237 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40237step0 raw40237; decide +kernel
      have hl : raw40237step0Labels = raw40237Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40237 raw40237Labels permutation283 permutation7
    mixedMoment B raw40237step0 raw40237step0Labels = mixedMoment B raw40237step1 raw40237step1Labels := by
      have ha : raw40237step1 = -raw40237step0 := by apply Matrix.ext; change ∀ i j, raw40237step1 i j = -(raw40237step0 i j); unfold raw40237step1 raw40237step0; decide +kernel
      have hl : raw40237step1Labels = raw40237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node520 node520Labels := by rfl

def raw40238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40238Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw40238step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40238step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40238 raw40238Labels = mixedMoment B node336 node336Labels := by
  calc
    mixedMoment B raw40238 raw40238Labels = mixedMoment B raw40238step0 raw40238step0Labels := by
      have hz : ∀ j, raw40238 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40238step0 = (fun i j => raw40238 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40238step0 raw40238; decide +kernel
      have hl : raw40238step0Labels = raw40238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40238 raw40238Labels permutation434 hz
    mixedMoment B raw40238step0 raw40238step0Labels = mixedMoment B raw40238step1 raw40238step1Labels := by
      have ha : raw40238step1 = (fun i j => raw40238step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40238step1 raw40238step0; decide +kernel
      have hl : raw40238step1Labels = raw40238step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40238step0 raw40238step0Labels permutation144 permutation7
    _ = mixedMoment B node336 node336Labels := by rfl

def raw40239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40239Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 2, -4]]
def raw40239step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40239step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40239 raw40239Labels = mixedMoment B node124 node124Labels := by
  calc
    mixedMoment B raw40239 raw40239Labels = mixedMoment B raw40239step0 raw40239step0Labels := by
      have hz : ∀ j, raw40239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40239step0 = (fun i j => raw40239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40239step0 raw40239; decide +kernel
      have hl : raw40239step0Labels = raw40239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40239 raw40239Labels permutation434 hz
    mixedMoment B raw40239step0 raw40239step0Labels = mixedMoment B raw40239step1 raw40239step1Labels := by
      have ha : raw40239step1 = (fun i j => raw40239step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40239step1 raw40239step0; decide +kernel
      have hl : raw40239step1Labels = raw40239step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40239step0 raw40239step0Labels permutation140 permutation6
    _ = mixedMoment B node124 node124Labels := by rfl

def raw40240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw40240Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -2, 1]]
def raw40240step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40240step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40240 raw40240Labels = mixedMoment B node312 node312Labels := by
  calc
    mixedMoment B raw40240 raw40240Labels = mixedMoment B raw40240step0 raw40240step0Labels := by
      have hz : ∀ j, raw40240 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40240step0 = (fun i j => raw40240 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40240step0 raw40240; decide +kernel
      have hl : raw40240step0Labels = raw40240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40240 raw40240Labels permutation434 hz
    mixedMoment B raw40240step0 raw40240step0Labels = mixedMoment B raw40240step1 raw40240step1Labels := by
      have ha : raw40240step1 = (fun i j => raw40240step0 (permutation117 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40240step1 raw40240step0; decide +kernel
      have hl : raw40240step1Labels = raw40240step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40240step0 raw40240step0Labels permutation117 permutation6
    _ = mixedMoment B node312 node312Labels := by rfl

def raw40241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40241Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw40241step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40241step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40241 raw40241Labels = mixedMoment B node521 node521Labels := by
  calc
    mixedMoment B raw40241 raw40241Labels = mixedMoment B raw40241step0 raw40241step0Labels := by
      have hz : ∀ j, raw40241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40241step0 = (fun i j => raw40241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40241step0 raw40241; decide +kernel
      have hl : raw40241step0Labels = raw40241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40241 raw40241Labels permutation434 hz
    mixedMoment B raw40241step0 raw40241step0Labels = mixedMoment B raw40241step1 raw40241step1Labels := by
      have ha : raw40241step1 = (fun i j => raw40241step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40241step1 raw40241step0; decide +kernel
      have hl : raw40241step1Labels = raw40241step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40241step0 raw40241step0Labels permutation120 permutation6
    _ = mixedMoment B node521 node521Labels := by rfl

def raw40242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40242Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40242step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40242 raw40242Labels = mixedMoment B node517 node517Labels := by
  calc
    mixedMoment B raw40242 raw40242Labels = mixedMoment B raw40242step0 raw40242step0Labels := by
      have ha : raw40242step0 = (fun i j => raw40242 (permutation548 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40242step0 raw40242; decide +kernel
      have hl : raw40242step0Labels = raw40242Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40242 raw40242Labels permutation548 permutation6
    _ = mixedMoment B node517 node517Labels := by rfl

def raw40243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40243Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40243step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40243step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40243 raw40243Labels = mixedMoment B node293 node293Labels := by
  calc
    mixedMoment B raw40243 raw40243Labels = mixedMoment B raw40243step0 raw40243step0Labels := by
      have ha : raw40243step0 = (fun i j => raw40243 (permutation547 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40243step0 raw40243; decide +kernel
      have hl : raw40243step0Labels = raw40243Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40243 raw40243Labels permutation547 permutation6
    _ = mixedMoment B node293 node293Labels := by rfl

def raw40244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw40244Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw40244step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 2, -4]]
def raw40244step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40244step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40244 raw40244Labels = mixedMoment B node157 node157Labels := by
  calc
    mixedMoment B raw40244 raw40244Labels = mixedMoment B raw40244step0 raw40244step0Labels := by
      have hz : ∀ j, raw40244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40244step0 = (fun i j => raw40244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40244step0 raw40244; decide +kernel
      have hl : raw40244step0Labels = raw40244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40244 raw40244Labels permutation434 hz
    mixedMoment B raw40244step0 raw40244step0Labels = mixedMoment B raw40244step1 raw40244step1Labels := by
      have hz : ∀ j, raw40244step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40244step1 = (fun i j => raw40244step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40244step1 raw40244step0; decide +kernel
      have hl : raw40244step1Labels = raw40244step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40244step0 raw40244step0Labels permutation80 hz
    mixedMoment B raw40244step1 raw40244step1Labels = mixedMoment B raw40244step2 raw40244step2Labels := by
      have ha : raw40244step2 = (fun i j => raw40244step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40244step2 raw40244step1; decide +kernel
      have hl : raw40244step2Labels = raw40244step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40244step1 raw40244step1Labels permutation27 permutation6
    _ = mixedMoment B node157 node157Labels := by rfl

def raw40245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40245Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40245step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![2, 3, -5]]
def raw40245step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40245step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40245 raw40245Labels = mixedMoment B node30 node30Labels := by
  calc
    mixedMoment B raw40245 raw40245Labels = mixedMoment B raw40245step0 raw40245step0Labels := by
      have hz : ∀ j, raw40245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40245step0 = (fun i j => raw40245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40245step0 raw40245; decide +kernel
      have hl : raw40245step0Labels = raw40245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40245 raw40245Labels permutation434 hz
    mixedMoment B raw40245step0 raw40245step0Labels = mixedMoment B raw40245step1 raw40245step1Labels := by
      have hz : ∀ j, raw40245step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40245step1 = (fun i j => raw40245step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40245step1 raw40245step0; decide +kernel
      have hl : raw40245step1Labels = raw40245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40245step0 raw40245step0Labels permutation80 hz
    mixedMoment B raw40245step1 raw40245step1Labels = mixedMoment B raw40245step2 raw40245step2Labels := by
      have ha : raw40245step2 = (fun i j => raw40245step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40245step2 raw40245step1; decide +kernel
      have hl : raw40245step2Labels = raw40245step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40245step1 raw40245step1Labels permutation26 permutation6
    _ = mixedMoment B node30 node30Labels := by rfl

def raw40246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw40246Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw40246step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40246step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40246 raw40246Labels = mixedMoment B node26 node26Labels := by
  calc
    mixedMoment B raw40246 raw40246Labels = mixedMoment B raw40246step0 raw40246step0Labels := by
      have hz : ∀ j, raw40246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40246step0 = (fun i j => raw40246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40246step0 raw40246; decide +kernel
      have hl : raw40246step0Labels = raw40246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40246 raw40246Labels permutation346 hz
    mixedMoment B raw40246step0 raw40246step0Labels = mixedMoment B raw40246step1 raw40246step1Labels := by
      have ha : raw40246step1 = (fun i j => raw40246step0 (permutation131 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40246step1 raw40246step0; decide +kernel
      have hl : raw40246step1Labels = raw40246step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40246step0 raw40246step0Labels permutation131 permutation6
    _ = mixedMoment B node26 node26Labels := by rfl

def raw40247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40247Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40247step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40247step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40247 raw40247Labels = mixedMoment B node93 node93Labels := by
  calc
    mixedMoment B raw40247 raw40247Labels = mixedMoment B raw40247step0 raw40247step0Labels := by
      have hz : ∀ j, raw40247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40247step0 = (fun i j => raw40247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40247step0 raw40247; decide +kernel
      have hl : raw40247step0Labels = raw40247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40247 raw40247Labels permutation346 hz
    mixedMoment B raw40247step0 raw40247step0Labels = mixedMoment B raw40247step1 raw40247step1Labels := by
      have ha : raw40247step1 = (fun i j => raw40247step0 (permutation123 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40247step1 raw40247step0; decide +kernel
      have hl : raw40247step1Labels = raw40247step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40247step0 raw40247step0Labels permutation123 permutation6
    _ = mixedMoment B node93 node93Labels := by rfl

def raw40248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40248Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40248step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40248step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40248 raw40248Labels = mixedMoment B node509 node509Labels := by
  calc
    mixedMoment B raw40248 raw40248Labels = mixedMoment B raw40248step0 raw40248step0Labels := by
      have hz : ∀ j, raw40248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40248step0 = (fun i j => raw40248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40248step0 raw40248; decide +kernel
      have hl : raw40248step0Labels = raw40248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40248 raw40248Labels permutation346 hz
    mixedMoment B raw40248step0 raw40248step0Labels = mixedMoment B raw40248step1 raw40248step1Labels := by
      have ha : raw40248step1 = (fun i j => raw40248step0 (permutation123 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40248step1 raw40248step0; decide +kernel
      have hl : raw40248step1Labels = raw40248step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40248step0 raw40248step0Labels permutation123 permutation6
    _ = mixedMoment B node509 node509Labels := by rfl

def raw40249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40249Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40249step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40249 raw40249Labels = mixedMoment B node63 node63Labels := by
  calc
    mixedMoment B raw40249 raw40249Labels = mixedMoment B raw40249step0 raw40249step0Labels := by
      have ha : raw40249step0 = (fun i j => raw40249 (permutation572 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40249step0 raw40249; decide +kernel
      have hl : raw40249step0Labels = raw40249Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40249 raw40249Labels permutation572 permutation6
    _ = mixedMoment B node63 node63Labels := by rfl

def raw40250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40250Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![2, -1, -1]]
def raw40250step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![2, -1, -1]]
def raw40250step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40250step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40250 raw40250Labels = mixedMoment B node247 node247Labels := by
  calc
    mixedMoment B raw40250 raw40250Labels = mixedMoment B raw40250step0 raw40250step0Labels := by
      have hz : ∀ j, raw40250 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40250step0 = (fun i j => raw40250 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40250step0 raw40250; decide +kernel
      have hl : raw40250step0Labels = raw40250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40250 raw40250Labels permutation520 hz
    mixedMoment B raw40250step0 raw40250step0Labels = mixedMoment B raw40250step1 raw40250step1Labels := by
      have hz : ∀ j, raw40250step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40250step1 = (fun i j => raw40250step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40250step1 raw40250step0; decide +kernel
      have hl : raw40250step1Labels = raw40250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40250step0 raw40250step0Labels permutation104 hz
    mixedMoment B raw40250step1 raw40250step1Labels = mixedMoment B raw40250step2 raw40250step2Labels := by
      have ha : raw40250step2 = (fun i j => raw40250step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40250step2 raw40250step1; decide +kernel
      have hl : raw40250step2Labels = raw40250step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40250step1 raw40250step1Labels permutation24 permutation6
    _ = mixedMoment B node247 node247Labels := by rfl

def raw40251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40251Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw40251step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40251step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40251 raw40251Labels = mixedMoment B node175 node175Labels := by
  calc
    mixedMoment B raw40251 raw40251Labels = mixedMoment B raw40251step0 raw40251step0Labels := by
      have hz : ∀ j, raw40251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40251step0 = (fun i j => raw40251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40251step0 raw40251; decide +kernel
      have hl : raw40251step0Labels = raw40251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40251 raw40251Labels permutation434 hz
    mixedMoment B raw40251step0 raw40251step0Labels = mixedMoment B raw40251step1 raw40251step1Labels := by
      have ha : raw40251step1 = (fun i j => raw40251step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40251step1 raw40251step0; decide +kernel
      have hl : raw40251step1Labels = raw40251step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40251step0 raw40251step0Labels permutation99 permutation6
    _ = mixedMoment B node175 node175Labels := by rfl

def raw40252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40252Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40252step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40252step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40252 raw40252Labels = mixedMoment B node222 node222Labels := by
  calc
    mixedMoment B raw40252 raw40252Labels = mixedMoment B raw40252step0 raw40252step0Labels := by
      have hz : ∀ j, raw40252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40252step0 = (fun i j => raw40252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40252step0 raw40252; decide +kernel
      have hl : raw40252step0Labels = raw40252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40252 raw40252Labels permutation434 hz
    mixedMoment B raw40252step0 raw40252step0Labels = mixedMoment B raw40252step1 raw40252step1Labels := by
      have ha : raw40252step1 = (fun i j => raw40252step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40252step1 raw40252step0; decide +kernel
      have hl : raw40252step1Labels = raw40252step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40252step0 raw40252step0Labels permutation96 permutation6
    _ = mixedMoment B node222 node222Labels := by rfl

def raw40253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw40253Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]
def raw40253step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40253step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40253step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40253 raw40253Labels = mixedMoment B node332 node332Labels := by
  calc
    mixedMoment B raw40253 raw40253Labels = mixedMoment B raw40253step0 raw40253step0Labels := by
      have hz : ∀ j, raw40253 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40253step0 = (fun i j => raw40253 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40253step0 raw40253; decide +kernel
      have hl : raw40253step0Labels = raw40253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40253 raw40253Labels permutation520 hz
    mixedMoment B raw40253step0 raw40253step0Labels = mixedMoment B raw40253step1 raw40253step1Labels := by
      have ha : raw40253step1 = (fun i j => raw40253step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40253step1 raw40253step0; decide +kernel
      have hl : raw40253step1Labels = raw40253step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40253step0 raw40253step0Labels permutation61 permutation6
    mixedMoment B raw40253step1 raw40253step1Labels = mixedMoment B raw40253step2 raw40253step2Labels := by
      have ha : raw40253step2 = -raw40253step1 := by apply Matrix.ext; change ∀ i j, raw40253step2 i j = -(raw40253step1 i j); unfold raw40253step2 raw40253step1; decide +kernel
      have hl : raw40253step2Labels = raw40253step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node332 node332Labels := by rfl

def raw40254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40254Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw40254step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![2, 0, -2]]
def raw40254step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40254step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw40254step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40254step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40254step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40254 raw40254Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw40254 raw40254Labels = mixedMoment B raw40254step0 raw40254step0Labels := by
      have hz : ∀ j, raw40254 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40254step0 = (fun i j => raw40254 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40254step0 raw40254; decide +kernel
      have hl : raw40254step0Labels = raw40254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40254 raw40254Labels permutation520 hz
    mixedMoment B raw40254step0 raw40254step0Labels = mixedMoment B raw40254step1 raw40254step1Labels := by
      have hz : ∀ j, raw40254step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40254step1 = (fun i j => raw40254step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40254step1 raw40254step0; decide +kernel
      have hl : raw40254step1Labels = raw40254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40254step0 raw40254step0Labels permutation104 hz
    mixedMoment B raw40254step1 raw40254step1Labels = mixedMoment B raw40254step2 raw40254step2Labels := by
      have ha : raw40254step2 = (fun i j => raw40254step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40254step2 raw40254step1; decide +kernel
      have hl : raw40254step2Labels = raw40254step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40254step1 raw40254step1Labels permutation15 permutation6
    mixedMoment B raw40254step2 raw40254step2Labels = mixedMoment B raw40254step3 raw40254step3Labels := by
      have ha : raw40254step3 = -raw40254step2 := by apply Matrix.ext; change ∀ i j, raw40254step3 i j = -(raw40254step2 i j); unfold raw40254step3 raw40254step2; decide +kernel
      have hl : raw40254step3Labels = raw40254step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node343 node343Labels := by rfl

def raw40255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40255Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw40255step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw40255step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40255 raw40255Labels = mixedMoment B node285 node285Labels := by
  calc
    mixedMoment B raw40255 raw40255Labels = mixedMoment B raw40255step0 raw40255step0Labels := by
      have hz : ∀ j, raw40255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40255step0 = (fun i j => raw40255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40255step0 raw40255; decide +kernel
      have hl : raw40255step0Labels = raw40255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40255 raw40255Labels permutation434 hz
    mixedMoment B raw40255step0 raw40255step0Labels = mixedMoment B raw40255step1 raw40255step1Labels := by
      have ha : raw40255step1 = (fun i j => raw40255step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40255step1 raw40255step0; decide +kernel
      have hl : raw40255step1Labels = raw40255step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40255step0 raw40255step0Labels permutation144 permutation7
    _ = mixedMoment B node285 node285Labels := by rfl

def raw40256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40256Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw40256step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40256step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40256step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40256 raw40256Labels = mixedMoment B node325 node325Labels := by
  calc
    mixedMoment B raw40256 raw40256Labels = mixedMoment B raw40256step0 raw40256step0Labels := by
      have hz : ∀ j, raw40256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40256step0 = (fun i j => raw40256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40256step0 raw40256; decide +kernel
      have hl : raw40256step0Labels = raw40256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40256 raw40256Labels permutation434 hz
    mixedMoment B raw40256step0 raw40256step0Labels = mixedMoment B raw40256step1 raw40256step1Labels := by
      have ha : raw40256step1 = (fun i j => raw40256step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40256step1 raw40256step0; decide +kernel
      have hl : raw40256step1Labels = raw40256step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40256step0 raw40256step0Labels permutation61 permutation6
    mixedMoment B raw40256step1 raw40256step1Labels = mixedMoment B raw40256step2 raw40256step2Labels := by
      have ha : raw40256step2 = -raw40256step1 := by apply Matrix.ext; change ∀ i j, raw40256step2 i j = -(raw40256step1 i j); unfold raw40256step2 raw40256step1; decide +kernel
      have hl : raw40256step2Labels = raw40256step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node325 node325Labels := by rfl

def raw40257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40257Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40257step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40257step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40257 raw40257Labels = mixedMoment B node293 node293Labels := by
  calc
    mixedMoment B raw40257 raw40257Labels = mixedMoment B raw40257step0 raw40257step0Labels := by
      have ha : raw40257step0 = (fun i j => raw40257 (permutation310 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40257step0 raw40257; decide +kernel
      have hl : raw40257step0Labels = raw40257Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40257 raw40257Labels permutation310 permutation6
    mixedMoment B raw40257step0 raw40257step0Labels = mixedMoment B raw40257step1 raw40257step1Labels := by
      have ha : raw40257step1 = -raw40257step0 := by apply Matrix.ext; change ∀ i j, raw40257step1 i j = -(raw40257step0 i j); unfold raw40257step1 raw40257step0; decide +kernel
      have hl : raw40257step1Labels = raw40257step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node293 node293Labels := by rfl

def raw40258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40258Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw40258step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40258step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40258step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40258 raw40258Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw40258 raw40258Labels = mixedMoment B raw40258step0 raw40258step0Labels := by
      have hz : ∀ j, raw40258 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40258step0 = (fun i j => raw40258 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40258step0 raw40258; decide +kernel
      have hl : raw40258step0Labels = raw40258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40258 raw40258Labels permutation520 hz
    mixedMoment B raw40258step0 raw40258step0Labels = mixedMoment B raw40258step1 raw40258step1Labels := by
      have ha : raw40258step1 = (fun i j => raw40258step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40258step1 raw40258step0; decide +kernel
      have hl : raw40258step1Labels = raw40258step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40258step0 raw40258step0Labels permutation56 permutation6
    mixedMoment B raw40258step1 raw40258step1Labels = mixedMoment B raw40258step2 raw40258step2Labels := by
      have ha : raw40258step2 = -raw40258step1 := by apply Matrix.ext; change ∀ i j, raw40258step2 i j = -(raw40258step1 i j); unfold raw40258step2 raw40258step1; decide +kernel
      have hl : raw40258step2Labels = raw40258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node339 node339Labels := by rfl

def raw40259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw40259Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40259step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40259step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40259 raw40259Labels = mixedMoment B node294 node294Labels := by
  calc
    mixedMoment B raw40259 raw40259Labels = mixedMoment B raw40259step0 raw40259step0Labels := by
      have ha : raw40259step0 = (fun i j => raw40259 (permutation322 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40259step0 raw40259; decide +kernel
      have hl : raw40259step0Labels = raw40259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40259 raw40259Labels permutation322 permutation6
    mixedMoment B raw40259step0 raw40259step0Labels = mixedMoment B raw40259step1 raw40259step1Labels := by
      have ha : raw40259step1 = -raw40259step0 := by apply Matrix.ext; change ∀ i j, raw40259step1 i j = -(raw40259step0 i j); unfold raw40259step1 raw40259step0; decide +kernel
      have hl : raw40259step1Labels = raw40259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node294 node294Labels := by rfl

def raw40260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw40260Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40260step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40260step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40260 raw40260Labels = mixedMoment B node321 node321Labels := by
  calc
    mixedMoment B raw40260 raw40260Labels = mixedMoment B raw40260step0 raw40260step0Labels := by
      have ha : raw40260step0 = (fun i j => raw40260 (permutation283 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40260step0 raw40260; decide +kernel
      have hl : raw40260step0Labels = raw40260Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40260 raw40260Labels permutation283 permutation6
    mixedMoment B raw40260step0 raw40260step0Labels = mixedMoment B raw40260step1 raw40260step1Labels := by
      have ha : raw40260step1 = -raw40260step0 := by apply Matrix.ext; change ∀ i j, raw40260step1 i j = -(raw40260step0 i j); unfold raw40260step1 raw40260step0; decide +kernel
      have hl : raw40260step1Labels = raw40260step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node321 node321Labels := by rfl

def raw40261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40261Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw40261step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![2, 1, -3]]
def raw40261step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw40261step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40261step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw40261step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40261 raw40261Labels = mixedMoment B node341 node341Labels := by
  calc
    mixedMoment B raw40261 raw40261Labels = mixedMoment B raw40261step0 raw40261step0Labels := by
      have hz : ∀ j, raw40261 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40261step0 = (fun i j => raw40261 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40261step0 raw40261; decide +kernel
      have hl : raw40261step0Labels = raw40261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40261 raw40261Labels permutation520 hz
    mixedMoment B raw40261step0 raw40261step0Labels = mixedMoment B raw40261step1 raw40261step1Labels := by
      have hz : ∀ j, raw40261step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40261step1 = (fun i j => raw40261step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40261step1 raw40261step0; decide +kernel
      have hl : raw40261step1Labels = raw40261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40261step0 raw40261step0Labels permutation104 hz
    mixedMoment B raw40261step1 raw40261step1Labels = mixedMoment B raw40261step2 raw40261step2Labels := by
      have ha : raw40261step2 = (fun i j => raw40261step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40261step2 raw40261step1; decide +kernel
      have hl : raw40261step2Labels = raw40261step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40261step1 raw40261step1Labels permutation14 permutation6
    mixedMoment B raw40261step2 raw40261step2Labels = mixedMoment B raw40261step3 raw40261step3Labels := by
      have ha : raw40261step3 = -raw40261step2 := by apply Matrix.ext; change ∀ i j, raw40261step3 i j = -(raw40261step2 i j); unfold raw40261step3 raw40261step2; decide +kernel
      have hl : raw40261step3Labels = raw40261step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node341 node341Labels := by rfl

def raw40262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40262Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]
def raw40262step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40262step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40262 raw40262Labels = mixedMoment B node303 node303Labels := by
  calc
    mixedMoment B raw40262 raw40262Labels = mixedMoment B raw40262step0 raw40262step0Labels := by
      have hz : ∀ j, raw40262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40262step0 = (fun i j => raw40262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40262step0 raw40262; decide +kernel
      have hl : raw40262step0Labels = raw40262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40262 raw40262Labels permutation434 hz
    mixedMoment B raw40262step0 raw40262step0Labels = mixedMoment B raw40262step1 raw40262step1Labels := by
      have ha : raw40262step1 = (fun i j => raw40262step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40262step1 raw40262step0; decide +kernel
      have hl : raw40262step1Labels = raw40262step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40262step0 raw40262step0Labels permutation120 permutation6
    _ = mixedMoment B node303 node303Labels := by rfl

def raw40263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40263Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40263step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40263 raw40263Labels = mixedMoment B node291 node291Labels := by
  calc
    mixedMoment B raw40263 raw40263Labels = mixedMoment B raw40263step0 raw40263step0Labels := by
      have ha : raw40263step0 = (fun i j => raw40263 (permutation548 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40263step0 raw40263; decide +kernel
      have hl : raw40263step0Labels = raw40263Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40263 raw40263Labels permutation548 permutation6
    _ = mixedMoment B node291 node291Labels := by rfl

def raw40264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40264Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40264step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![2, 2, -4]]
def raw40264step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40264step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![2, 2, -4]]
def raw40264step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40264step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw40264step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40264 raw40264Labels = mixedMoment B node158 node158Labels := by
  calc
    mixedMoment B raw40264 raw40264Labels = mixedMoment B raw40264step0 raw40264step0Labels := by
      have hz : ∀ j, raw40264 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40264step0 = (fun i j => raw40264 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40264step0 raw40264; decide +kernel
      have hl : raw40264step0Labels = raw40264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40264 raw40264Labels permutation520 hz
    mixedMoment B raw40264step0 raw40264step0Labels = mixedMoment B raw40264step1 raw40264step1Labels := by
      have hz : ∀ j, raw40264step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40264step1 = (fun i j => raw40264step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40264step1 raw40264step0; decide +kernel
      have hl : raw40264step1Labels = raw40264step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40264step0 raw40264step0Labels permutation104 hz
    mixedMoment B raw40264step1 raw40264step1Labels = mixedMoment B raw40264step2 raw40264step2Labels := by
      have hz : ∀ j, raw40264step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40264step2 = (fun i j => raw40264step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40264step2 raw40264step1; decide +kernel
      have hl : raw40264step2Labels = raw40264step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40264step1 raw40264step1Labels permutation20 hz
    mixedMoment B raw40264step2 raw40264step2Labels = mixedMoment B raw40264step3 raw40264step3Labels := by
      have ha : raw40264step3 = (fun i j => raw40264step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40264step3 raw40264step2; decide +kernel
      have hl : raw40264step3Labels = raw40264step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40264step2 raw40264step2Labels permutation6 permutation6
    _ = mixedMoment B node158 node158Labels := by rfl

def raw40265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40265Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40265step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![2, 3, -5]]
def raw40265step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40265step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40265 raw40265Labels = mixedMoment B node28 node28Labels := by
  calc
    mixedMoment B raw40265 raw40265Labels = mixedMoment B raw40265step0 raw40265step0Labels := by
      have hz : ∀ j, raw40265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40265step0 = (fun i j => raw40265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40265step0 raw40265; decide +kernel
      have hl : raw40265step0Labels = raw40265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40265 raw40265Labels permutation434 hz
    mixedMoment B raw40265step0 raw40265step0Labels = mixedMoment B raw40265step1 raw40265step1Labels := by
      have hz : ∀ j, raw40265step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40265step1 = (fun i j => raw40265step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40265step1 raw40265step0; decide +kernel
      have hl : raw40265step1Labels = raw40265step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40265step0 raw40265step0Labels permutation80 hz
    mixedMoment B raw40265step1 raw40265step1Labels = mixedMoment B raw40265step2 raw40265step2Labels := by
      have ha : raw40265step2 = (fun i j => raw40265step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40265step2 raw40265step1; decide +kernel
      have hl : raw40265step2Labels = raw40265step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40265step1 raw40265step1Labels permutation27 permutation6
    _ = mixedMoment B node28 node28Labels := by rfl

def raw40266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40266Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40266step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![1, 3, -4], ![1, -1, 0]]
def raw40266step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40266step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40266step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40266 raw40266Labels = mixedMoment B node94 node94Labels := by
  calc
    mixedMoment B raw40266 raw40266Labels = mixedMoment B raw40266step0 raw40266step0Labels := by
      have hz : ∀ j, raw40266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40266step0 = (fun i j => raw40266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40266step0 raw40266; decide +kernel
      have hl : raw40266step0Labels = raw40266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40266 raw40266Labels permutation434 hz
    mixedMoment B raw40266step0 raw40266step0Labels = mixedMoment B raw40266step1 raw40266step1Labels := by
      have hz : ∀ j, raw40266step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40266step1 = (fun i j => raw40266step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40266step1 raw40266step0; decide +kernel
      have hl : raw40266step1Labels = raw40266step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40266step0 raw40266step0Labels permutation80 hz
    mixedMoment B raw40266step1 raw40266step1Labels = mixedMoment B raw40266step2 raw40266step2Labels := by
      have ha : raw40266step2 = (fun i j => raw40266step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40266step2 raw40266step1; decide +kernel
      have hl : raw40266step2Labels = raw40266step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40266step1 raw40266step1Labels permutation24 permutation6
    _ = mixedMoment B node94 node94Labels := by rfl

def raw40267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40267Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw40267step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![2, 0, -2]]
def raw40267step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 2, 0], ![-3, 0, 3]]
def raw40267step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw40267step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40267 raw40267Labels = mixedMoment B node71 node71Labels := by
  calc
    mixedMoment B raw40267 raw40267Labels = mixedMoment B raw40267step0 raw40267step0Labels := by
      have hz : ∀ j, raw40267 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40267step0 = (fun i j => raw40267 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40267step0 raw40267; decide +kernel
      have hl : raw40267step0Labels = raw40267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40267 raw40267Labels permutation520 hz
    mixedMoment B raw40267step0 raw40267step0Labels = mixedMoment B raw40267step1 raw40267step1Labels := by
      have hz : ∀ j, raw40267step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40267step1 = (fun i j => raw40267step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40267step1 raw40267step0; decide +kernel
      have hl : raw40267step1Labels = raw40267step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40267step0 raw40267step0Labels permutation104 hz
    mixedMoment B raw40267step1 raw40267step1Labels = mixedMoment B raw40267step2 raw40267step2Labels := by
      have ha : raw40267step2 = (fun i j => raw40267step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40267step2 raw40267step1; decide +kernel
      have hl : raw40267step2Labels = raw40267step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40267step1 raw40267step1Labels permutation15 permutation6
    mixedMoment B raw40267step2 raw40267step2Labels = mixedMoment B raw40267step3 raw40267step3Labels := by
      have ha : raw40267step3 = -raw40267step2 := by apply Matrix.ext; change ∀ i j, raw40267step3 i j = -(raw40267step2 i j); unfold raw40267step3 raw40267step2; decide +kernel
      have hl : raw40267step3Labels = raw40267step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node71 node71Labels := by rfl

def raw40268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40268Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw40268step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40268step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40268step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40268 raw40268Labels = mixedMoment B node68 node68Labels := by
  calc
    mixedMoment B raw40268 raw40268Labels = mixedMoment B raw40268step0 raw40268step0Labels := by
      have hz : ∀ j, raw40268 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40268step0 = (fun i j => raw40268 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40268step0 raw40268; decide +kernel
      have hl : raw40268step0Labels = raw40268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40268 raw40268Labels permutation520 hz
    mixedMoment B raw40268step0 raw40268step0Labels = mixedMoment B raw40268step1 raw40268step1Labels := by
      have ha : raw40268step1 = (fun i j => raw40268step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40268step1 raw40268step0; decide +kernel
      have hl : raw40268step1Labels = raw40268step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40268step0 raw40268step0Labels permutation59 permutation6
    mixedMoment B raw40268step1 raw40268step1Labels = mixedMoment B raw40268step2 raw40268step2Labels := by
      have ha : raw40268step2 = -raw40268step1 := by apply Matrix.ext; change ∀ i j, raw40268step2 i j = -(raw40268step1 i j); unfold raw40268step2 raw40268step1; decide +kernel
      have hl : raw40268step2Labels = raw40268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node68 node68Labels := by rfl

def raw40269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40269Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw40269step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![2, 1, -3]]
def raw40269step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw40269step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40269step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw40269step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40269 raw40269Labels = mixedMoment B node72 node72Labels := by
  calc
    mixedMoment B raw40269 raw40269Labels = mixedMoment B raw40269step0 raw40269step0Labels := by
      have hz : ∀ j, raw40269 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40269step0 = (fun i j => raw40269 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40269step0 raw40269; decide +kernel
      have hl : raw40269step0Labels = raw40269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40269 raw40269Labels permutation520 hz
    mixedMoment B raw40269step0 raw40269step0Labels = mixedMoment B raw40269step1 raw40269step1Labels := by
      have hz : ∀ j, raw40269step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40269step1 = (fun i j => raw40269step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40269step1 raw40269step0; decide +kernel
      have hl : raw40269step1Labels = raw40269step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40269step0 raw40269step0Labels permutation104 hz
    mixedMoment B raw40269step1 raw40269step1Labels = mixedMoment B raw40269step2 raw40269step2Labels := by
      have ha : raw40269step2 = (fun i j => raw40269step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40269step2 raw40269step1; decide +kernel
      have hl : raw40269step2Labels = raw40269step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40269step1 raw40269step1Labels permutation14 permutation6
    mixedMoment B raw40269step2 raw40269step2Labels = mixedMoment B raw40269step3 raw40269step3Labels := by
      have ha : raw40269step3 = -raw40269step2 := by apply Matrix.ext; change ∀ i j, raw40269step3 i j = -(raw40269step2 i j); unfold raw40269step3 raw40269step2; decide +kernel
      have hl : raw40269step3Labels = raw40269step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node72 node72Labels := by rfl

def raw40270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40270Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![2, 2, -4]]
def raw40270step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![2, 2, -4]]
def raw40270step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw40270step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40270step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw40270step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40270 raw40270Labels = mixedMoment B node70 node70Labels := by
  calc
    mixedMoment B raw40270 raw40270Labels = mixedMoment B raw40270step0 raw40270step0Labels := by
      have hz : ∀ j, raw40270 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40270step0 = (fun i j => raw40270 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40270step0 raw40270; decide +kernel
      have hl : raw40270step0Labels = raw40270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40270 raw40270Labels permutation520 hz
    mixedMoment B raw40270step0 raw40270step0Labels = mixedMoment B raw40270step1 raw40270step1Labels := by
      have hz : ∀ j, raw40270step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40270step1 = (fun i j => raw40270step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40270step1 raw40270step0; decide +kernel
      have hl : raw40270step1Labels = raw40270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40270step0 raw40270step0Labels permutation104 hz
    mixedMoment B raw40270step1 raw40270step1Labels = mixedMoment B raw40270step2 raw40270step2Labels := by
      have ha : raw40270step2 = (fun i j => raw40270step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40270step2 raw40270step1; decide +kernel
      have hl : raw40270step2Labels = raw40270step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40270step1 raw40270step1Labels permutation14 permutation6
    mixedMoment B raw40270step2 raw40270step2Labels = mixedMoment B raw40270step3 raw40270step3Labels := by
      have ha : raw40270step3 = -raw40270step2 := by apply Matrix.ext; change ∀ i j, raw40270step3 i j = -(raw40270step2 i j); unfold raw40270step3 raw40270step2; decide +kernel
      have hl : raw40270step3Labels = raw40270step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node70 node70Labels := by rfl

def raw40271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40271Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![2, -1, -1]]
def raw40271step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![2, -1, -1]]
def raw40271step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40271step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40271 raw40271Labels = mixedMoment B node252 node252Labels := by
  calc
    mixedMoment B raw40271 raw40271Labels = mixedMoment B raw40271step0 raw40271step0Labels := by
      have hz : ∀ j, raw40271 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40271step0 = (fun i j => raw40271 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40271step0 raw40271; decide +kernel
      have hl : raw40271step0Labels = raw40271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40271 raw40271Labels permutation520 hz
    mixedMoment B raw40271step0 raw40271step0Labels = mixedMoment B raw40271step1 raw40271step1Labels := by
      have hz : ∀ j, raw40271step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40271step1 = (fun i j => raw40271step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40271step1 raw40271step0; decide +kernel
      have hl : raw40271step1Labels = raw40271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40271step0 raw40271step0Labels permutation104 hz
    mixedMoment B raw40271step1 raw40271step1Labels = mixedMoment B raw40271step2 raw40271step2Labels := by
      have ha : raw40271step2 = (fun i j => raw40271step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40271step2 raw40271step1; decide +kernel
      have hl : raw40271step2Labels = raw40271step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40271step1 raw40271step1Labels permutation24 permutation6
    _ = mixedMoment B node252 node252Labels := by rfl

def raw40272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40272Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw40272step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40272step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40272 raw40272Labels = mixedMoment B node183 node183Labels := by
  calc
    mixedMoment B raw40272 raw40272Labels = mixedMoment B raw40272step0 raw40272step0Labels := by
      have hz : ∀ j, raw40272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40272step0 = (fun i j => raw40272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40272step0 raw40272; decide +kernel
      have hl : raw40272step0Labels = raw40272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40272 raw40272Labels permutation434 hz
    mixedMoment B raw40272step0 raw40272step0Labels = mixedMoment B raw40272step1 raw40272step1Labels := by
      have ha : raw40272step1 = (fun i j => raw40272step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40272step1 raw40272step0; decide +kernel
      have hl : raw40272step1Labels = raw40272step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40272step0 raw40272step0Labels permutation102 permutation6
    _ = mixedMoment B node183 node183Labels := by rfl

def raw40273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40273Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40273step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40273step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40273 raw40273Labels = mixedMoment B node227 node227Labels := by
  calc
    mixedMoment B raw40273 raw40273Labels = mixedMoment B raw40273step0 raw40273step0Labels := by
      have hz : ∀ j, raw40273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40273step0 = (fun i j => raw40273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40273step0 raw40273; decide +kernel
      have hl : raw40273step0Labels = raw40273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40273 raw40273Labels permutation434 hz
    mixedMoment B raw40273step0 raw40273step0Labels = mixedMoment B raw40273step1 raw40273step1Labels := by
      have ha : raw40273step1 = (fun i j => raw40273step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40273step1 raw40273step0; decide +kernel
      have hl : raw40273step1Labels = raw40273step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40273step0 raw40273step0Labels permutation96 permutation6
    _ = mixedMoment B node227 node227Labels := by rfl

def raw40274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40274Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40274step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40274 raw40274Labels = mixedMoment B node210 node210Labels := by
  calc
    mixedMoment B raw40274 raw40274Labels = mixedMoment B raw40274step0 raw40274step0Labels := by
      have ha : raw40274step0 = (fun i j => raw40274 (permutation413 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40274step0 raw40274; decide +kernel
      have hl : raw40274step0Labels = raw40274Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40274 raw40274Labels permutation413 permutation6
    _ = mixedMoment B node210 node210Labels := by rfl

def raw40275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40275Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw40275step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, 0, -2]]
def raw40275step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw40275step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40275 raw40275Labels = mixedMoment B node452 node452Labels := by
  calc
    mixedMoment B raw40275 raw40275Labels = mixedMoment B raw40275step0 raw40275step0Labels := by
      have hz : ∀ j, raw40275 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40275step0 = (fun i j => raw40275 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40275step0 raw40275; decide +kernel
      have hl : raw40275step0Labels = raw40275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40275 raw40275Labels permutation520 hz
    mixedMoment B raw40275step0 raw40275step0Labels = mixedMoment B raw40275step1 raw40275step1Labels := by
      have hz : ∀ j, raw40275step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40275step1 = (fun i j => raw40275step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40275step1 raw40275step0; decide +kernel
      have hl : raw40275step1Labels = raw40275step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40275step0 raw40275step0Labels permutation104 hz
    mixedMoment B raw40275step1 raw40275step1Labels = mixedMoment B raw40275step2 raw40275step2Labels := by
      have ha : raw40275step2 = (fun i j => raw40275step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40275step2 raw40275step1; decide +kernel
      have hl : raw40275step2Labels = raw40275step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40275step1 raw40275step1Labels permutation24 permutation6
    _ = mixedMoment B node452 node452Labels := by rfl

def raw40276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40276Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40276step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40276step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40276 raw40276Labels = mixedMoment B node508 node508Labels := by
  calc
    mixedMoment B raw40276 raw40276Labels = mixedMoment B raw40276step0 raw40276step0Labels := by
      have ha : raw40276step0 = (fun i j => raw40276 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40276step0 raw40276; decide +kernel
      have hl : raw40276step0Labels = raw40276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40276 raw40276Labels permutation168 permutation6
    mixedMoment B raw40276step0 raw40276step0Labels = mixedMoment B raw40276step1 raw40276step1Labels := by
      have ha : raw40276step1 = -raw40276step0 := by apply Matrix.ext; change ∀ i j, raw40276step1 i j = -(raw40276step0 i j); unfold raw40276step1 raw40276step0; decide +kernel
      have hl : raw40276step1Labels = raw40276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node508 node508Labels := by rfl

def raw40277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw40277Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]
def raw40277step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw40277step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40277step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40277 raw40277Labels = mixedMoment B node509 node509Labels := by
  calc
    mixedMoment B raw40277 raw40277Labels = mixedMoment B raw40277step0 raw40277step0Labels := by
      have hz : ∀ j, raw40277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40277step0 = (fun i j => raw40277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40277step0 raw40277; decide +kernel
      have hl : raw40277step0Labels = raw40277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40277 raw40277Labels permutation434 hz
    mixedMoment B raw40277step0 raw40277step0Labels = mixedMoment B raw40277step1 raw40277step1Labels := by
      have ha : raw40277step1 = (fun i j => raw40277step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40277step1 raw40277step0; decide +kernel
      have hl : raw40277step1Labels = raw40277step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40277step0 raw40277step0Labels permutation36 permutation6
    mixedMoment B raw40277step1 raw40277step1Labels = mixedMoment B raw40277step2 raw40277step2Labels := by
      have ha : raw40277step2 = -raw40277step1 := by apply Matrix.ext; change ∀ i j, raw40277step2 i j = -(raw40277step1 i j); unfold raw40277step2 raw40277step1; decide +kernel
      have hl : raw40277step2Labels = raw40277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node509 node509Labels := by rfl

def raw40278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40278Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40278step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![2, 2, -4]]
def raw40278step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![2, 2, -4]]
def raw40278step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40278step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw40278step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40278 raw40278Labels = mixedMoment B node161 node161Labels := by
  calc
    mixedMoment B raw40278 raw40278Labels = mixedMoment B raw40278step0 raw40278step0Labels := by
      have hz : ∀ j, raw40278 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40278step0 = (fun i j => raw40278 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40278step0 raw40278; decide +kernel
      have hl : raw40278step0Labels = raw40278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40278 raw40278Labels permutation520 hz
    mixedMoment B raw40278step0 raw40278step0Labels = mixedMoment B raw40278step1 raw40278step1Labels := by
      have hz : ∀ j, raw40278step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40278step1 = (fun i j => raw40278step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40278step1 raw40278step0; decide +kernel
      have hl : raw40278step1Labels = raw40278step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40278step0 raw40278step0Labels permutation104 hz
    mixedMoment B raw40278step1 raw40278step1Labels = mixedMoment B raw40278step2 raw40278step2Labels := by
      have hz : ∀ j, raw40278step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40278step2 = (fun i j => raw40278step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40278step2 raw40278step1; decide +kernel
      have hl : raw40278step2Labels = raw40278step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40278step1 raw40278step1Labels permutation20 hz
    mixedMoment B raw40278step2 raw40278step2Labels = mixedMoment B raw40278step3 raw40278step3Labels := by
      have ha : raw40278step3 = (fun i j => raw40278step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40278step3 raw40278step2; decide +kernel
      have hl : raw40278step3Labels = raw40278step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40278step2 raw40278step2Labels permutation6 permutation6
    _ = mixedMoment B node161 node161Labels := by rfl

def raw40279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40279Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40279step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 3, -5]]
def raw40279step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40279step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40279step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40279 raw40279Labels = mixedMoment B node34 node34Labels := by
  calc
    mixedMoment B raw40279 raw40279Labels = mixedMoment B raw40279step0 raw40279step0Labels := by
      have hz : ∀ j, raw40279 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40279step0 = (fun i j => raw40279 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40279step0 raw40279; decide +kernel
      have hl : raw40279step0Labels = raw40279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40279 raw40279Labels permutation434 hz
    mixedMoment B raw40279step0 raw40279step0Labels = mixedMoment B raw40279step1 raw40279step1Labels := by
      have hz : ∀ j, raw40279step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40279step1 = (fun i j => raw40279step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40279step1 raw40279step0; decide +kernel
      have hl : raw40279step1Labels = raw40279step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40279step0 raw40279step0Labels permutation80 hz
    mixedMoment B raw40279step1 raw40279step1Labels = mixedMoment B raw40279step2 raw40279step2Labels := by
      have ha : raw40279step2 = (fun i j => raw40279step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40279step2 raw40279step1; decide +kernel
      have hl : raw40279step2Labels = raw40279step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40279step1 raw40279step1Labels permutation30 permutation6
    _ = mixedMoment B node34 node34Labels := by rfl

def raw40280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40280Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40280step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0]]
def raw40280step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40280step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40280step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40280 raw40280Labels = mixedMoment B node99 node99Labels := by
  calc
    mixedMoment B raw40280 raw40280Labels = mixedMoment B raw40280step0 raw40280step0Labels := by
      have hz : ∀ j, raw40280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40280step0 = (fun i j => raw40280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40280step0 raw40280; decide +kernel
      have hl : raw40280step0Labels = raw40280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40280 raw40280Labels permutation434 hz
    mixedMoment B raw40280step0 raw40280step0Labels = mixedMoment B raw40280step1 raw40280step1Labels := by
      have hz : ∀ j, raw40280step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40280step1 = (fun i j => raw40280step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40280step1 raw40280step0; decide +kernel
      have hl : raw40280step1Labels = raw40280step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40280step0 raw40280step0Labels permutation80 hz
    mixedMoment B raw40280step1 raw40280step1Labels = mixedMoment B raw40280step2 raw40280step2Labels := by
      have ha : raw40280step2 = (fun i j => raw40280step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40280step2 raw40280step1; decide +kernel
      have hl : raw40280step2Labels = raw40280step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40280step1 raw40280step1Labels permutation24 permutation6
    _ = mixedMoment B node99 node99Labels := by rfl

def raw40281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw40281Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw40281step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def raw40281step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw40281step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40281 raw40281Labels = mixedMoment B node510 node510Labels := by
  calc
    mixedMoment B raw40281 raw40281Labels = mixedMoment B raw40281step0 raw40281step0Labels := by
      have hz : ∀ j, raw40281 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40281step0 = (fun i j => raw40281 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40281step0 raw40281; decide +kernel
      have hl : raw40281step0Labels = raw40281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40281 raw40281Labels permutation434 hz
    mixedMoment B raw40281step0 raw40281step0Labels = mixedMoment B raw40281step1 raw40281step1Labels := by
      have hz : ∀ j, raw40281step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40281step1 = (fun i j => raw40281step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40281step1 raw40281step0; decide +kernel
      have hl : raw40281step1Labels = raw40281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40281step0 raw40281step0Labels permutation80 hz
    mixedMoment B raw40281step1 raw40281step1Labels = mixedMoment B raw40281step2 raw40281step2Labels := by
      have ha : raw40281step2 = (fun i j => raw40281step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40281step2 raw40281step1; decide +kernel
      have hl : raw40281step2Labels = raw40281step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40281step1 raw40281step1Labels permutation24 permutation6
    _ = mixedMoment B node510 node510Labels := by rfl

def raw40282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40282Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40282step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40282step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40282 raw40282Labels = mixedMoment B node69 node69Labels := by
  calc
    mixedMoment B raw40282 raw40282Labels = mixedMoment B raw40282step0 raw40282step0Labels := by
      have hz : ∀ j, raw40282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40282step0 = (fun i j => raw40282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40282step0 raw40282; decide +kernel
      have hl : raw40282step0Labels = raw40282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40282 raw40282Labels permutation346 hz
    mixedMoment B raw40282step0 raw40282step0Labels = mixedMoment B raw40282step1 raw40282step1Labels := by
      have ha : raw40282step1 = (fun i j => raw40282step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40282step1 raw40282step0; decide +kernel
      have hl : raw40282step1Labels = raw40282step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40282step0 raw40282step0Labels permutation126 permutation6
    _ = mixedMoment B node69 node69Labels := by rfl

def raw40283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40283Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw40283step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![2, 0, -2]]
def raw40283step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw40283step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40283 raw40283Labels = mixedMoment B node186 node186Labels := by
  calc
    mixedMoment B raw40283 raw40283Labels = mixedMoment B raw40283step0 raw40283step0Labels := by
      have hz : ∀ j, raw40283 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40283step0 = (fun i j => raw40283 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40283step0 raw40283; decide +kernel
      have hl : raw40283step0Labels = raw40283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40283 raw40283Labels permutation520 hz
    mixedMoment B raw40283step0 raw40283step0Labels = mixedMoment B raw40283step1 raw40283step1Labels := by
      have hz : ∀ j, raw40283step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40283step1 = (fun i j => raw40283step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40283step1 raw40283step0; decide +kernel
      have hl : raw40283step1Labels = raw40283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40283step0 raw40283step0Labels permutation104 hz
    mixedMoment B raw40283step1 raw40283step1Labels = mixedMoment B raw40283step2 raw40283step2Labels := by
      have ha : raw40283step2 = (fun i j => raw40283step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40283step2 raw40283step1; decide +kernel
      have hl : raw40283step2Labels = raw40283step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40283step1 raw40283step1Labels permutation24 permutation6
    _ = mixedMoment B node186 node186Labels := by rfl

def raw40284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40284Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw40284step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40284step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40284step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40284 raw40284Labels = mixedMoment B node275 node275Labels := by
  calc
    mixedMoment B raw40284 raw40284Labels = mixedMoment B raw40284step0 raw40284step0Labels := by
      have hz : ∀ j, raw40284 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40284step0 = (fun i j => raw40284 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40284step0 raw40284; decide +kernel
      have hl : raw40284step0Labels = raw40284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40284 raw40284Labels permutation520 hz
    mixedMoment B raw40284step0 raw40284step0Labels = mixedMoment B raw40284step1 raw40284step1Labels := by
      have ha : raw40284step1 = (fun i j => raw40284step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40284step1 raw40284step0; decide +kernel
      have hl : raw40284step1Labels = raw40284step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40284step0 raw40284step0Labels permutation59 permutation6
    mixedMoment B raw40284step1 raw40284step1Labels = mixedMoment B raw40284step2 raw40284step2Labels := by
      have ha : raw40284step2 = -raw40284step1 := by apply Matrix.ext; change ∀ i j, raw40284step2 i j = -(raw40284step1 i j); unfold raw40284step2 raw40284step1; decide +kernel
      have hl : raw40284step2Labels = raw40284step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node275 node275Labels := by rfl

def raw40285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40285Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw40285step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![2, 1, -3]]
def raw40285step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40285step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40285step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40285step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40285 raw40285Labels = mixedMoment B node277 node277Labels := by
  calc
    mixedMoment B raw40285 raw40285Labels = mixedMoment B raw40285step0 raw40285step0Labels := by
      have hz : ∀ j, raw40285 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40285step0 = (fun i j => raw40285 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40285step0 raw40285; decide +kernel
      have hl : raw40285step0Labels = raw40285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40285 raw40285Labels permutation520 hz
    mixedMoment B raw40285step0 raw40285step0Labels = mixedMoment B raw40285step1 raw40285step1Labels := by
      have hz : ∀ j, raw40285step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40285step1 = (fun i j => raw40285step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40285step1 raw40285step0; decide +kernel
      have hl : raw40285step1Labels = raw40285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40285step0 raw40285step0Labels permutation104 hz
    mixedMoment B raw40285step1 raw40285step1Labels = mixedMoment B raw40285step2 raw40285step2Labels := by
      have ha : raw40285step2 = (fun i j => raw40285step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40285step2 raw40285step1; decide +kernel
      have hl : raw40285step2Labels = raw40285step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40285step1 raw40285step1Labels permutation14 permutation6
    mixedMoment B raw40285step2 raw40285step2Labels = mixedMoment B raw40285step3 raw40285step3Labels := by
      have ha : raw40285step3 = -raw40285step2 := by apply Matrix.ext; change ∀ i j, raw40285step3 i j = -(raw40285step2 i j); unfold raw40285step3 raw40285step2; decide +kernel
      have hl : raw40285step3Labels = raw40285step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node277 node277Labels := by rfl

def raw40286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw40286Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw40286step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![2, 3, -5]]
def raw40286step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40286step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![2, 3, -5]]
def raw40286step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40286step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw40286step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40286 raw40286Labels = mixedMoment B node39 node39Labels := by
  calc
    mixedMoment B raw40286 raw40286Labels = mixedMoment B raw40286step0 raw40286step0Labels := by
      have hz : ∀ j, raw40286 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40286step0 = (fun i j => raw40286 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40286step0 raw40286; decide +kernel
      have hl : raw40286step0Labels = raw40286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40286 raw40286Labels permutation520 hz
    mixedMoment B raw40286step0 raw40286step0Labels = mixedMoment B raw40286step1 raw40286step1Labels := by
      have hz : ∀ j, raw40286step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40286step1 = (fun i j => raw40286step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40286step1 raw40286step0; decide +kernel
      have hl : raw40286step1Labels = raw40286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40286step0 raw40286step0Labels permutation104 hz
    mixedMoment B raw40286step1 raw40286step1Labels = mixedMoment B raw40286step2 raw40286step2Labels := by
      have hz : ∀ j, raw40286step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40286step2 = (fun i j => raw40286step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40286step2 raw40286step1; decide +kernel
      have hl : raw40286step2Labels = raw40286step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40286step1 raw40286step1Labels permutation20 hz
    mixedMoment B raw40286step2 raw40286step2Labels = mixedMoment B raw40286step3 raw40286step3Labels := by
      have ha : raw40286step3 = (fun i j => raw40286step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40286step3 raw40286step2; decide +kernel
      have hl : raw40286step3Labels = raw40286step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40286step2 raw40286step2Labels permutation6 permutation6
    _ = mixedMoment B node39 node39Labels := by rfl

def raw40287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40287step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40287step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40287step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40287step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw40287step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40287 raw40287Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw40287 raw40287Labels = mixedMoment B raw40287step0 raw40287step0Labels := by
      have hz : ∀ j, raw40287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40287step0 = (fun i j => raw40287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40287step0 raw40287; decide +kernel
      have hl : raw40287step0Labels = raw40287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40287 raw40287Labels permutation434 hz
    mixedMoment B raw40287step0 raw40287step0Labels = mixedMoment B raw40287step1 raw40287step1Labels := by
      have hz : ∀ j, raw40287step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40287step1 = (fun i j => raw40287step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40287step1 raw40287step0; decide +kernel
      have hl : raw40287step1Labels = raw40287step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40287step0 raw40287step0Labels permutation80 hz
    mixedMoment B raw40287step1 raw40287step1Labels = mixedMoment B raw40287step2 raw40287step2Labels := by
      have hz : ∀ j, raw40287step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40287step2 = (fun i j => raw40287step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40287step2 raw40287step1; decide +kernel
      have hl : raw40287step2Labels = raw40287step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40287step1 raw40287step1Labels permutation14 hz
    mixedMoment B raw40287step2 raw40287step2Labels = mixedMoment B raw40287step3 raw40287step3Labels := by
      have ha : raw40287step3 = (fun i j => raw40287step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40287step3 raw40287step2; decide +kernel
      have hl : raw40287step3Labels = raw40287step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40287step2 raw40287step2Labels permutation2 permutation3
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw40288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40288step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40288step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40288step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40288step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw40288step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40288 raw40288Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw40288 raw40288Labels = mixedMoment B raw40288step0 raw40288step0Labels := by
      have hz : ∀ j, raw40288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40288step0 = (fun i j => raw40288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40288step0 raw40288; decide +kernel
      have hl : raw40288step0Labels = raw40288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40288 raw40288Labels permutation434 hz
    mixedMoment B raw40288step0 raw40288step0Labels = mixedMoment B raw40288step1 raw40288step1Labels := by
      have hz : ∀ j, raw40288step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40288step1 = (fun i j => raw40288step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40288step1 raw40288step0; decide +kernel
      have hl : raw40288step1Labels = raw40288step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40288step0 raw40288step0Labels permutation80 hz
    mixedMoment B raw40288step1 raw40288step1Labels = mixedMoment B raw40288step2 raw40288step2Labels := by
      have hz : ∀ j, raw40288step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40288step2 = (fun i j => raw40288step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40288step2 raw40288step1; decide +kernel
      have hl : raw40288step2Labels = raw40288step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40288step1 raw40288step1Labels permutation14 hz
    mixedMoment B raw40288step2 raw40288step2Labels = mixedMoment B raw40288step3 raw40288step3Labels := by
      have ha : raw40288step3 = (fun i j => raw40288step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40288step3 raw40288step2; decide +kernel
      have hl : raw40288step3Labels = raw40288step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40288step2 raw40288step2Labels permutation2 permutation3
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw40289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40289step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40289step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40289step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40289step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw40289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40289 raw40289Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw40289 raw40289Labels = mixedMoment B raw40289step0 raw40289step0Labels := by
      have hz : ∀ j, raw40289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40289step0 = (fun i j => raw40289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40289step0 raw40289; decide +kernel
      have hl : raw40289step0Labels = raw40289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40289 raw40289Labels permutation434 hz
    mixedMoment B raw40289step0 raw40289step0Labels = mixedMoment B raw40289step1 raw40289step1Labels := by
      have hz : ∀ j, raw40289step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40289step1 = (fun i j => raw40289step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40289step1 raw40289step0; decide +kernel
      have hl : raw40289step1Labels = raw40289step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40289step0 raw40289step0Labels permutation80 hz
    mixedMoment B raw40289step1 raw40289step1Labels = mixedMoment B raw40289step2 raw40289step2Labels := by
      have hz : ∀ j, raw40289step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40289step2 = (fun i j => raw40289step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40289step2 raw40289step1; decide +kernel
      have hl : raw40289step2Labels = raw40289step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40289step1 raw40289step1Labels permutation14 hz
    mixedMoment B raw40289step2 raw40289step2Labels = mixedMoment B raw40289step3 raw40289step3Labels := by
      have ha : raw40289step3 = (fun i j => raw40289step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40289step3 raw40289step2; decide +kernel
      have hl : raw40289step3Labels = raw40289step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40289step2 raw40289step2Labels permutation2 permutation3
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw40290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40290step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40290step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40290step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40290step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40290step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw40290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40290 raw40290Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw40290 raw40290Labels = mixedMoment B raw40290step0 raw40290step0Labels := by
      have hz : ∀ j, raw40290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40290step0 = (fun i j => raw40290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40290step0 raw40290; decide +kernel
      have hl : raw40290step0Labels = raw40290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40290 raw40290Labels permutation434 hz
    mixedMoment B raw40290step0 raw40290step0Labels = mixedMoment B raw40290step1 raw40290step1Labels := by
      have hz : ∀ j, raw40290step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40290step1 = (fun i j => raw40290step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40290step1 raw40290step0; decide +kernel
      have hl : raw40290step1Labels = raw40290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40290step0 raw40290step0Labels permutation80 hz
    mixedMoment B raw40290step1 raw40290step1Labels = mixedMoment B raw40290step2 raw40290step2Labels := by
      have hz : ∀ j, raw40290step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40290step2 = (fun i j => raw40290step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40290step2 raw40290step1; decide +kernel
      have hl : raw40290step2Labels = raw40290step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40290step1 raw40290step1Labels permutation14 hz
    mixedMoment B raw40290step2 raw40290step2Labels = mixedMoment B raw40290step3 raw40290step3Labels := by
      have ha : raw40290step3 = (fun i j => raw40290step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40290step3 raw40290step2; decide +kernel
      have hl : raw40290step3Labels = raw40290step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40290step2 raw40290step2Labels permutation2 permutation3
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw40291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40291step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40291step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40291 raw40291Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw40291 raw40291Labels = mixedMoment B raw40291step0 raw40291step0Labels := by
      have hz : ∀ j, raw40291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40291step0 = (fun i j => raw40291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40291step0 raw40291; decide +kernel
      have hl : raw40291step0Labels = raw40291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40291 raw40291Labels permutation346 hz
    mixedMoment B raw40291step0 raw40291step0Labels = mixedMoment B raw40291step1 raw40291step1Labels := by
      have hz : ∀ j, raw40291step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40291step1 = (fun i j => raw40291step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40291step1 raw40291step0; decide +kernel
      have hl : raw40291step1Labels = raw40291step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40291step0 raw40291step0Labels permutation56 hz
    mixedMoment B raw40291step1 raw40291step1Labels = mixedMoment B raw40291step2 raw40291step2Labels := by
      have ha : raw40291step2 = (fun i j => raw40291step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40291step2 raw40291step1; decide +kernel
      have hl : raw40291step2Labels = raw40291step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40291step1 raw40291step1Labels permutation8 permutation3
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw40292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40292step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40292step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40292 raw40292Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw40292 raw40292Labels = mixedMoment B raw40292step0 raw40292step0Labels := by
      have hz : ∀ j, raw40292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40292step0 = (fun i j => raw40292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40292step0 raw40292; decide +kernel
      have hl : raw40292step0Labels = raw40292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40292 raw40292Labels permutation346 hz
    mixedMoment B raw40292step0 raw40292step0Labels = mixedMoment B raw40292step1 raw40292step1Labels := by
      have hz : ∀ j, raw40292step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40292step1 = (fun i j => raw40292step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40292step1 raw40292step0; decide +kernel
      have hl : raw40292step1Labels = raw40292step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40292step0 raw40292step0Labels permutation56 hz
    mixedMoment B raw40292step1 raw40292step1Labels = mixedMoment B raw40292step2 raw40292step2Labels := by
      have ha : raw40292step2 = (fun i j => raw40292step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40292step2 raw40292step1; decide +kernel
      have hl : raw40292step2Labels = raw40292step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40292step1 raw40292step1Labels permutation8 permutation3
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw40293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40293step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40293step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40293 raw40293Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw40293 raw40293Labels = mixedMoment B raw40293step0 raw40293step0Labels := by
      have hz : ∀ j, raw40293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40293step0 = (fun i j => raw40293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40293step0 raw40293; decide +kernel
      have hl : raw40293step0Labels = raw40293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40293 raw40293Labels permutation346 hz
    mixedMoment B raw40293step0 raw40293step0Labels = mixedMoment B raw40293step1 raw40293step1Labels := by
      have hz : ∀ j, raw40293step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40293step1 = (fun i j => raw40293step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40293step1 raw40293step0; decide +kernel
      have hl : raw40293step1Labels = raw40293step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40293step0 raw40293step0Labels permutation56 hz
    mixedMoment B raw40293step1 raw40293step1Labels = mixedMoment B raw40293step2 raw40293step2Labels := by
      have ha : raw40293step2 = (fun i j => raw40293step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40293step2 raw40293step1; decide +kernel
      have hl : raw40293step2Labels = raw40293step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40293step1 raw40293step1Labels permutation8 permutation3
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw40294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40294step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40294 raw40294Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw40294 raw40294Labels = mixedMoment B raw40294step0 raw40294step0Labels := by
      have hz : ∀ j, raw40294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40294step0 = (fun i j => raw40294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40294step0 raw40294; decide +kernel
      have hl : raw40294step0Labels = raw40294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40294 raw40294Labels permutation346 hz
    mixedMoment B raw40294step0 raw40294step0Labels = mixedMoment B raw40294step1 raw40294step1Labels := by
      have hz : ∀ j, raw40294step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40294step1 = (fun i j => raw40294step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40294step1 raw40294step0; decide +kernel
      have hl : raw40294step1Labels = raw40294step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40294step0 raw40294step0Labels permutation56 hz
    mixedMoment B raw40294step1 raw40294step1Labels = mixedMoment B raw40294step2 raw40294step2Labels := by
      have ha : raw40294step2 = (fun i j => raw40294step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40294step2 raw40294step1; decide +kernel
      have hl : raw40294step2Labels = raw40294step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40294step1 raw40294step1Labels permutation8 permutation3
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw40295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40295step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40295 raw40295Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw40295 raw40295Labels = mixedMoment B raw40295step0 raw40295step0Labels := by
      have hz : ∀ j, raw40295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40295step0 = (fun i j => raw40295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40295step0 raw40295; decide +kernel
      have hl : raw40295step0Labels = raw40295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40295 raw40295Labels permutation346 hz
    mixedMoment B raw40295step0 raw40295step0Labels = mixedMoment B raw40295step1 raw40295step1Labels := by
      have hz : ∀ j, raw40295step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40295step1 = (fun i j => raw40295step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40295step1 raw40295step0; decide +kernel
      have hl : raw40295step1Labels = raw40295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40295step0 raw40295step0Labels permutation56 hz
    mixedMoment B raw40295step1 raw40295step1Labels = mixedMoment B raw40295step2 raw40295step2Labels := by
      have ha : raw40295step2 = (fun i j => raw40295step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40295step2 raw40295step1; decide +kernel
      have hl : raw40295step2Labels = raw40295step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40295step1 raw40295step1Labels permutation8 permutation3
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw40296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40296step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40296 raw40296Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw40296 raw40296Labels = mixedMoment B raw40296step0 raw40296step0Labels := by
      have hz : ∀ j, raw40296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40296step0 = (fun i j => raw40296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40296step0 raw40296; decide +kernel
      have hl : raw40296step0Labels = raw40296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40296 raw40296Labels permutation346 hz
    mixedMoment B raw40296step0 raw40296step0Labels = mixedMoment B raw40296step1 raw40296step1Labels := by
      have hz : ∀ j, raw40296step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40296step1 = (fun i j => raw40296step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40296step1 raw40296step0; decide +kernel
      have hl : raw40296step1Labels = raw40296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40296step0 raw40296step0Labels permutation56 hz
    mixedMoment B raw40296step1 raw40296step1Labels = mixedMoment B raw40296step2 raw40296step2Labels := by
      have ha : raw40296step2 = (fun i j => raw40296step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40296step2 raw40296step1; decide +kernel
      have hl : raw40296step2Labels = raw40296step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40296step1 raw40296step1Labels permutation8 permutation3
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw40297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40297step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40297 raw40297Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw40297 raw40297Labels = mixedMoment B raw40297step0 raw40297step0Labels := by
      have hz : ∀ j, raw40297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40297step0 = (fun i j => raw40297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40297step0 raw40297; decide +kernel
      have hl : raw40297step0Labels = raw40297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40297 raw40297Labels permutation346 hz
    mixedMoment B raw40297step0 raw40297step0Labels = mixedMoment B raw40297step1 raw40297step1Labels := by
      have hz : ∀ j, raw40297step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40297step1 = (fun i j => raw40297step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40297step1 raw40297step0; decide +kernel
      have hl : raw40297step1Labels = raw40297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40297step0 raw40297step0Labels permutation56 hz
    mixedMoment B raw40297step1 raw40297step1Labels = mixedMoment B raw40297step2 raw40297step2Labels := by
      have ha : raw40297step2 = (fun i j => raw40297step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40297step2 raw40297step1; decide +kernel
      have hl : raw40297step2Labels = raw40297step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40297step1 raw40297step1Labels permutation8 permutation3
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw40298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40298 raw40298Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw40298 raw40298Labels = mixedMoment B raw40298step0 raw40298step0Labels := by
      have hz : ∀ j, raw40298 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40298step0 = (fun i j => raw40298 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40298step0 raw40298; decide +kernel
      have hl : raw40298step0Labels = raw40298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40298 raw40298Labels permutation265 hz
    mixedMoment B raw40298step0 raw40298step0Labels = mixedMoment B raw40298step1 raw40298step1Labels := by
      have ha : raw40298step1 = (fun i j => raw40298step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40298step1 raw40298step0; decide +kernel
      have hl : raw40298step1Labels = raw40298step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40298step0 raw40298step0Labels permutation32 permutation3
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw40299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40299 raw40299Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw40299 raw40299Labels = mixedMoment B raw40299step0 raw40299step0Labels := by
      have hz : ∀ j, raw40299 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40299step0 = (fun i j => raw40299 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40299step0 raw40299; decide +kernel
      have hl : raw40299step0Labels = raw40299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40299 raw40299Labels permutation265 hz
    mixedMoment B raw40299step0 raw40299step0Labels = mixedMoment B raw40299step1 raw40299step1Labels := by
      have ha : raw40299step1 = (fun i j => raw40299step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40299step1 raw40299step0; decide +kernel
      have hl : raw40299step1Labels = raw40299step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40299step0 raw40299step0Labels permutation32 permutation3
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw40300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40300 raw40300Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw40300 raw40300Labels = mixedMoment B raw40300step0 raw40300step0Labels := by
      have hz : ∀ j, raw40300 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40300step0 = (fun i j => raw40300 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40300step0 raw40300; decide +kernel
      have hl : raw40300step0Labels = raw40300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40300 raw40300Labels permutation265 hz
    mixedMoment B raw40300step0 raw40300step0Labels = mixedMoment B raw40300step1 raw40300step1Labels := by
      have ha : raw40300step1 = (fun i j => raw40300step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40300step1 raw40300step0; decide +kernel
      have hl : raw40300step1Labels = raw40300step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40300step0 raw40300step0Labels permutation32 permutation3
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw40301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40301 raw40301Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw40301 raw40301Labels = mixedMoment B raw40301step0 raw40301step0Labels := by
      have hz : ∀ j, raw40301 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40301step0 = (fun i j => raw40301 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40301step0 raw40301; decide +kernel
      have hl : raw40301step0Labels = raw40301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40301 raw40301Labels permutation265 hz
    mixedMoment B raw40301step0 raw40301step0Labels = mixedMoment B raw40301step1 raw40301step1Labels := by
      have ha : raw40301step1 = (fun i j => raw40301step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40301step1 raw40301step0; decide +kernel
      have hl : raw40301step1Labels = raw40301step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40301step0 raw40301step0Labels permutation32 permutation3
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw40302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40302 raw40302Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw40302 raw40302Labels = mixedMoment B raw40302step0 raw40302step0Labels := by
      have hz : ∀ j, raw40302 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40302step0 = (fun i j => raw40302 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40302step0 raw40302; decide +kernel
      have hl : raw40302step0Labels = raw40302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40302 raw40302Labels permutation265 hz
    mixedMoment B raw40302step0 raw40302step0Labels = mixedMoment B raw40302step1 raw40302step1Labels := by
      have ha : raw40302step1 = (fun i j => raw40302step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40302step1 raw40302step0; decide +kernel
      have hl : raw40302step1Labels = raw40302step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40302step0 raw40302step0Labels permutation32 permutation3
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw40303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40303 raw40303Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw40303 raw40303Labels = mixedMoment B raw40303step0 raw40303step0Labels := by
      have ha : raw40303step0 = (fun i j => raw40303 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40303step0 raw40303; decide +kernel
      have hl : raw40303step0Labels = raw40303Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40303 raw40303Labels permutation152 permutation3
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw40304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40304step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw40304step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40304step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw40304step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40304step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw40304step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40304 raw40304Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw40304 raw40304Labels = mixedMoment B raw40304step0 raw40304step0Labels := by
      have hz : ∀ j, raw40304 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40304step0 = (fun i j => raw40304 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40304step0 raw40304; decide +kernel
      have hl : raw40304step0Labels = raw40304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40304 raw40304Labels permutation520 hz
    mixedMoment B raw40304step0 raw40304step0Labels = mixedMoment B raw40304step1 raw40304step1Labels := by
      have hz : ∀ j, raw40304step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40304step1 = (fun i j => raw40304step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40304step1 raw40304step0; decide +kernel
      have hl : raw40304step1Labels = raw40304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40304step0 raw40304step0Labels permutation104 hz
    mixedMoment B raw40304step1 raw40304step1Labels = mixedMoment B raw40304step2 raw40304step2Labels := by
      have hz : ∀ j, raw40304step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40304step2 = (fun i j => raw40304step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40304step2 raw40304step1; decide +kernel
      have hl : raw40304step2Labels = raw40304step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40304step1 raw40304step1Labels permutation20 hz
    mixedMoment B raw40304step2 raw40304step2Labels = mixedMoment B raw40304step3 raw40304step3Labels := by
      have ha : raw40304step3 = (fun i j => raw40304step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40304step3 raw40304step2; decide +kernel
      have hl : raw40304step3Labels = raw40304step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40304step2 raw40304step2Labels permutation7 permutation3
    mixedMoment B raw40304step3 raw40304step3Labels = mixedMoment B raw40304step4 raw40304step4Labels := by
      have ha : raw40304step4 = -raw40304step3 := by apply Matrix.ext; change ∀ i j, raw40304step4 i j = -(raw40304step3 i j); unfold raw40304step4 raw40304step3; decide +kernel
      have hl : raw40304step4Labels = raw40304step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw40305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40305step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40305step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40305 raw40305Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw40305 raw40305Labels = mixedMoment B raw40305step0 raw40305step0Labels := by
      have hz : ∀ j, raw40305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40305step0 = (fun i j => raw40305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40305step0 raw40305; decide +kernel
      have hl : raw40305step0Labels = raw40305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40305 raw40305Labels permutation434 hz
    mixedMoment B raw40305step0 raw40305step0Labels = mixedMoment B raw40305step1 raw40305step1Labels := by
      have hz : ∀ j, raw40305step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40305step1 = (fun i j => raw40305step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40305step1 raw40305step0; decide +kernel
      have hl : raw40305step1Labels = raw40305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40305step0 raw40305step0Labels permutation80 hz
    mixedMoment B raw40305step1 raw40305step1Labels = mixedMoment B raw40305step2 raw40305step2Labels := by
      have ha : raw40305step2 = (fun i j => raw40305step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40305step2 raw40305step1; decide +kernel
      have hl : raw40305step2Labels = raw40305step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40305step1 raw40305step1Labels permutation8 permutation3
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw40306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40306step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40306 raw40306Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw40306 raw40306Labels = mixedMoment B raw40306step0 raw40306step0Labels := by
      have hz : ∀ j, raw40306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40306step0 = (fun i j => raw40306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40306step0 raw40306; decide +kernel
      have hl : raw40306step0Labels = raw40306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40306 raw40306Labels permutation434 hz
    mixedMoment B raw40306step0 raw40306step0Labels = mixedMoment B raw40306step1 raw40306step1Labels := by
      have hz : ∀ j, raw40306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40306step1 = (fun i j => raw40306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40306step1 raw40306step0; decide +kernel
      have hl : raw40306step1Labels = raw40306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40306step0 raw40306step0Labels permutation80 hz
    mixedMoment B raw40306step1 raw40306step1Labels = mixedMoment B raw40306step2 raw40306step2Labels := by
      have ha : raw40306step2 = (fun i j => raw40306step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40306step2 raw40306step1; decide +kernel
      have hl : raw40306step2Labels = raw40306step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40306step1 raw40306step1Labels permutation8 permutation3
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw40307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40307step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40307 raw40307Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw40307 raw40307Labels = mixedMoment B raw40307step0 raw40307step0Labels := by
      have hz : ∀ j, raw40307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40307step0 = (fun i j => raw40307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40307step0 raw40307; decide +kernel
      have hl : raw40307step0Labels = raw40307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40307 raw40307Labels permutation434 hz
    mixedMoment B raw40307step0 raw40307step0Labels = mixedMoment B raw40307step1 raw40307step1Labels := by
      have hz : ∀ j, raw40307step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40307step1 = (fun i j => raw40307step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40307step1 raw40307step0; decide +kernel
      have hl : raw40307step1Labels = raw40307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40307step0 raw40307step0Labels permutation80 hz
    mixedMoment B raw40307step1 raw40307step1Labels = mixedMoment B raw40307step2 raw40307step2Labels := by
      have ha : raw40307step2 = (fun i j => raw40307step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40307step2 raw40307step1; decide +kernel
      have hl : raw40307step2Labels = raw40307step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40307step1 raw40307step1Labels permutation8 permutation3
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw40308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40308step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40308step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40308 raw40308Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw40308 raw40308Labels = mixedMoment B raw40308step0 raw40308step0Labels := by
      have hz : ∀ j, raw40308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40308step0 = (fun i j => raw40308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40308step0 raw40308; decide +kernel
      have hl : raw40308step0Labels = raw40308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40308 raw40308Labels permutation434 hz
    mixedMoment B raw40308step0 raw40308step0Labels = mixedMoment B raw40308step1 raw40308step1Labels := by
      have hz : ∀ j, raw40308step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40308step1 = (fun i j => raw40308step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40308step1 raw40308step0; decide +kernel
      have hl : raw40308step1Labels = raw40308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40308step0 raw40308step0Labels permutation80 hz
    mixedMoment B raw40308step1 raw40308step1Labels = mixedMoment B raw40308step2 raw40308step2Labels := by
      have ha : raw40308step2 = (fun i j => raw40308step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40308step2 raw40308step1; decide +kernel
      have hl : raw40308step2Labels = raw40308step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40308step1 raw40308step1Labels permutation8 permutation3
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw40309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40309 raw40309Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw40309 raw40309Labels = mixedMoment B raw40309step0 raw40309step0Labels := by
      have hz : ∀ j, raw40309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40309step0 = (fun i j => raw40309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40309step0 raw40309; decide +kernel
      have hl : raw40309step0Labels = raw40309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40309 raw40309Labels permutation346 hz
    mixedMoment B raw40309step0 raw40309step0Labels = mixedMoment B raw40309step1 raw40309step1Labels := by
      have ha : raw40309step1 = (fun i j => raw40309step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40309step1 raw40309step0; decide +kernel
      have hl : raw40309step1Labels = raw40309step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40309step0 raw40309step0Labels permutation32 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw40310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40310 raw40310Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw40310 raw40310Labels = mixedMoment B raw40310step0 raw40310step0Labels := by
      have hz : ∀ j, raw40310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40310step0 = (fun i j => raw40310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40310step0 raw40310; decide +kernel
      have hl : raw40310step0Labels = raw40310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40310 raw40310Labels permutation346 hz
    mixedMoment B raw40310step0 raw40310step0Labels = mixedMoment B raw40310step1 raw40310step1Labels := by
      have ha : raw40310step1 = (fun i j => raw40310step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40310step1 raw40310step0; decide +kernel
      have hl : raw40310step1Labels = raw40310step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40310step0 raw40310step0Labels permutation32 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw40311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40311 raw40311Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw40311 raw40311Labels = mixedMoment B raw40311step0 raw40311step0Labels := by
      have hz : ∀ j, raw40311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40311step0 = (fun i j => raw40311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40311step0 raw40311; decide +kernel
      have hl : raw40311step0Labels = raw40311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40311 raw40311Labels permutation346 hz
    mixedMoment B raw40311step0 raw40311step0Labels = mixedMoment B raw40311step1 raw40311step1Labels := by
      have ha : raw40311step1 = (fun i j => raw40311step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40311step1 raw40311step0; decide +kernel
      have hl : raw40311step1Labels = raw40311step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40311step0 raw40311step0Labels permutation32 permutation3
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw40312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40312 raw40312Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw40312 raw40312Labels = mixedMoment B raw40312step0 raw40312step0Labels := by
      have hz : ∀ j, raw40312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40312step0 = (fun i j => raw40312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40312step0 raw40312; decide +kernel
      have hl : raw40312step0Labels = raw40312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40312 raw40312Labels permutation346 hz
    mixedMoment B raw40312step0 raw40312step0Labels = mixedMoment B raw40312step1 raw40312step1Labels := by
      have ha : raw40312step1 = (fun i j => raw40312step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40312step1 raw40312step0; decide +kernel
      have hl : raw40312step1Labels = raw40312step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40312step0 raw40312step0Labels permutation32 permutation3
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw40313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40313 raw40313Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw40313 raw40313Labels = mixedMoment B raw40313step0 raw40313step0Labels := by
      have hz : ∀ j, raw40313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40313step0 = (fun i j => raw40313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40313step0 raw40313; decide +kernel
      have hl : raw40313step0Labels = raw40313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40313 raw40313Labels permutation346 hz
    mixedMoment B raw40313step0 raw40313step0Labels = mixedMoment B raw40313step1 raw40313step1Labels := by
      have ha : raw40313step1 = (fun i j => raw40313step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40313step1 raw40313step0; decide +kernel
      have hl : raw40313step1Labels = raw40313step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40313step0 raw40313step0Labels permutation32 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw40314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40314step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw40314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40314 raw40314Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw40314 raw40314Labels = mixedMoment B raw40314step0 raw40314step0Labels := by
      have hz : ∀ j, raw40314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40314step0 = (fun i j => raw40314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40314step0 raw40314; decide +kernel
      have hl : raw40314step0Labels = raw40314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40314 raw40314Labels permutation346 hz
    mixedMoment B raw40314step0 raw40314step0Labels = mixedMoment B raw40314step1 raw40314step1Labels := by
      have ha : raw40314step1 = (fun i j => raw40314step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40314step1 raw40314step0; decide +kernel
      have hl : raw40314step1Labels = raw40314step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40314step0 raw40314step0Labels permutation32 permutation3
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw40315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40315 raw40315Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw40315 raw40315Labels = mixedMoment B raw40315step0 raw40315step0Labels := by
      have hz : ∀ j, raw40315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40315step0 = (fun i j => raw40315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40315step0 raw40315; decide +kernel
      have hl : raw40315step0Labels = raw40315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40315 raw40315Labels permutation346 hz
    mixedMoment B raw40315step0 raw40315step0Labels = mixedMoment B raw40315step1 raw40315step1Labels := by
      have ha : raw40315step1 = (fun i j => raw40315step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40315step1 raw40315step0; decide +kernel
      have hl : raw40315step1Labels = raw40315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40315step0 raw40315step0Labels permutation32 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw40316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40316 raw40316Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw40316 raw40316Labels = mixedMoment B raw40316step0 raw40316step0Labels := by
      have hz : ∀ j, raw40316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40316step0 = (fun i j => raw40316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40316step0 raw40316; decide +kernel
      have hl : raw40316step0Labels = raw40316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40316 raw40316Labels permutation346 hz
    mixedMoment B raw40316step0 raw40316step0Labels = mixedMoment B raw40316step1 raw40316step1Labels := by
      have ha : raw40316step1 = (fun i j => raw40316step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40316step1 raw40316step0; decide +kernel
      have hl : raw40316step1Labels = raw40316step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40316step0 raw40316step0Labels permutation32 permutation3
    _ = mixedMoment B node2741 node2741Labels := by rfl

def raw40317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40317 raw40317Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw40317 raw40317Labels = mixedMoment B raw40317step0 raw40317step0Labels := by
      have ha : raw40317step0 = (fun i j => raw40317 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40317step0 raw40317; decide +kernel
      have hl : raw40317step0Labels = raw40317Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40317 raw40317Labels permutation152 permutation3
    _ = mixedMoment B node2709 node2709Labels := by rfl

def raw40318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40318 raw40318Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw40318 raw40318Labels = mixedMoment B raw40318step0 raw40318step0Labels := by
      have ha : raw40318step0 = (fun i j => raw40318 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40318step0 raw40318; decide +kernel
      have hl : raw40318step0Labels = raw40318Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40318 raw40318Labels permutation152 permutation3
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw40319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40319 raw40319Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw40319 raw40319Labels = mixedMoment B raw40319step0 raw40319step0Labels := by
      have ha : raw40319step0 = (fun i j => raw40319 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40319step0 raw40319; decide +kernel
      have hl : raw40319step0Labels = raw40319Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40319 raw40319Labels permutation152 permutation3
    _ = mixedMoment B node2720 node2720Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
