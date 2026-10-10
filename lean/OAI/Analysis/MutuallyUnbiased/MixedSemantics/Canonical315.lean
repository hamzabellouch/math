import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40320 raw40320Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw40320 raw40320Labels = mixedMoment B raw40320step0 raw40320step0Labels := by
      have ha : raw40320step0 = (fun i j => raw40320 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40320step0 raw40320; decide +kernel
      have hl : raw40320step0Labels = raw40320Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40320 raw40320Labels permutation152 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw40321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40321 raw40321Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw40321 raw40321Labels = mixedMoment B raw40321step0 raw40321step0Labels := by
      have ha : raw40321step0 = (fun i j => raw40321 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40321step0 raw40321; decide +kernel
      have hl : raw40321step0Labels = raw40321Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40321 raw40321Labels permutation152 permutation3
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw40322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40322step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40322step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw40322step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40322step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw40322step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40322 raw40322Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw40322 raw40322Labels = mixedMoment B raw40322step0 raw40322step0Labels := by
      have hz : ∀ j, raw40322 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40322step0 = (fun i j => raw40322 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40322step0 raw40322; decide +kernel
      have hl : raw40322step0Labels = raw40322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40322 raw40322Labels permutation434 hz
    mixedMoment B raw40322step0 raw40322step0Labels = mixedMoment B raw40322step1 raw40322step1Labels := by
      have hz : ∀ j, raw40322step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40322step1 = (fun i j => raw40322step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40322step1 raw40322step0; decide +kernel
      have hl : raw40322step1Labels = raw40322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40322step0 raw40322step0Labels permutation80 hz
    mixedMoment B raw40322step1 raw40322step1Labels = mixedMoment B raw40322step2 raw40322step2Labels := by
      have hz : ∀ j, raw40322step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40322step2 = (fun i j => raw40322step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40322step2 raw40322step1; decide +kernel
      have hl : raw40322step2Labels = raw40322step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40322step1 raw40322step1Labels permutation14 hz
    mixedMoment B raw40322step2 raw40322step2Labels = mixedMoment B raw40322step3 raw40322step3Labels := by
      have ha : raw40322step3 = (fun i j => raw40322step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40322step3 raw40322step2; decide +kernel
      have hl : raw40322step3Labels = raw40322step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40322step2 raw40322step2Labels permutation2 permutation3
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw40323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40323step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40323step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40323 raw40323Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw40323 raw40323Labels = mixedMoment B raw40323step0 raw40323step0Labels := by
      have hz : ∀ j, raw40323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40323step0 = (fun i j => raw40323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40323step0 raw40323; decide +kernel
      have hl : raw40323step0Labels = raw40323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40323 raw40323Labels permutation346 hz
    mixedMoment B raw40323step0 raw40323step0Labels = mixedMoment B raw40323step1 raw40323step1Labels := by
      have hz : ∀ j, raw40323step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40323step1 = (fun i j => raw40323step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40323step1 raw40323step0; decide +kernel
      have hl : raw40323step1Labels = raw40323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40323step0 raw40323step0Labels permutation56 hz
    mixedMoment B raw40323step1 raw40323step1Labels = mixedMoment B raw40323step2 raw40323step2Labels := by
      have ha : raw40323step2 = (fun i j => raw40323step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40323step2 raw40323step1; decide +kernel
      have hl : raw40323step2Labels = raw40323step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40323step1 raw40323step1Labels permutation8 permutation3
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw40324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40324step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40324 raw40324Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw40324 raw40324Labels = mixedMoment B raw40324step0 raw40324step0Labels := by
      have hz : ∀ j, raw40324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40324step0 = (fun i j => raw40324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40324step0 raw40324; decide +kernel
      have hl : raw40324step0Labels = raw40324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40324 raw40324Labels permutation346 hz
    mixedMoment B raw40324step0 raw40324step0Labels = mixedMoment B raw40324step1 raw40324step1Labels := by
      have hz : ∀ j, raw40324step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40324step1 = (fun i j => raw40324step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40324step1 raw40324step0; decide +kernel
      have hl : raw40324step1Labels = raw40324step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40324step0 raw40324step0Labels permutation56 hz
    mixedMoment B raw40324step1 raw40324step1Labels = mixedMoment B raw40324step2 raw40324step2Labels := by
      have ha : raw40324step2 = (fun i j => raw40324step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40324step2 raw40324step1; decide +kernel
      have hl : raw40324step2Labels = raw40324step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40324step1 raw40324step1Labels permutation8 permutation3
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw40325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40325step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40325step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40325step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40325step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw40325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40325 raw40325Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw40325 raw40325Labels = mixedMoment B raw40325step0 raw40325step0Labels := by
      have hz : ∀ j, raw40325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40325step0 = (fun i j => raw40325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40325step0 raw40325; decide +kernel
      have hl : raw40325step0Labels = raw40325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40325 raw40325Labels permutation346 hz
    mixedMoment B raw40325step0 raw40325step0Labels = mixedMoment B raw40325step1 raw40325step1Labels := by
      have hz : ∀ j, raw40325step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40325step1 = (fun i j => raw40325step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40325step1 raw40325step0; decide +kernel
      have hl : raw40325step1Labels = raw40325step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40325step0 raw40325step0Labels permutation56 hz
    mixedMoment B raw40325step1 raw40325step1Labels = mixedMoment B raw40325step2 raw40325step2Labels := by
      have ha : raw40325step2 = (fun i j => raw40325step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40325step2 raw40325step1; decide +kernel
      have hl : raw40325step2Labels = raw40325step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40325step1 raw40325step1Labels permutation8 permutation3
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw40326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40326step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw40326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40326 raw40326Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw40326 raw40326Labels = mixedMoment B raw40326step0 raw40326step0Labels := by
      have hz : ∀ j, raw40326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40326step0 = (fun i j => raw40326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40326step0 raw40326; decide +kernel
      have hl : raw40326step0Labels = raw40326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40326 raw40326Labels permutation346 hz
    mixedMoment B raw40326step0 raw40326step0Labels = mixedMoment B raw40326step1 raw40326step1Labels := by
      have hz : ∀ j, raw40326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40326step1 = (fun i j => raw40326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40326step1 raw40326step0; decide +kernel
      have hl : raw40326step1Labels = raw40326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40326step0 raw40326step0Labels permutation56 hz
    mixedMoment B raw40326step1 raw40326step1Labels = mixedMoment B raw40326step2 raw40326step2Labels := by
      have ha : raw40326step2 = (fun i j => raw40326step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40326step2 raw40326step1; decide +kernel
      have hl : raw40326step2Labels = raw40326step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40326step1 raw40326step1Labels permutation8 permutation3
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw40327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40327step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40327step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40327 raw40327Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw40327 raw40327Labels = mixedMoment B raw40327step0 raw40327step0Labels := by
      have hz : ∀ j, raw40327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40327step0 = (fun i j => raw40327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40327step0 raw40327; decide +kernel
      have hl : raw40327step0Labels = raw40327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40327 raw40327Labels permutation346 hz
    mixedMoment B raw40327step0 raw40327step0Labels = mixedMoment B raw40327step1 raw40327step1Labels := by
      have hz : ∀ j, raw40327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40327step1 = (fun i j => raw40327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40327step1 raw40327step0; decide +kernel
      have hl : raw40327step1Labels = raw40327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40327step0 raw40327step0Labels permutation56 hz
    mixedMoment B raw40327step1 raw40327step1Labels = mixedMoment B raw40327step2 raw40327step2Labels := by
      have ha : raw40327step2 = (fun i j => raw40327step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40327step2 raw40327step1; decide +kernel
      have hl : raw40327step2Labels = raw40327step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40327step1 raw40327step1Labels permutation8 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw40328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40328 raw40328Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw40328 raw40328Labels = mixedMoment B raw40328step0 raw40328step0Labels := by
      have hz : ∀ j, raw40328 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40328step0 = (fun i j => raw40328 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40328step0 raw40328; decide +kernel
      have hl : raw40328step0Labels = raw40328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40328 raw40328Labels permutation265 hz
    mixedMoment B raw40328step0 raw40328step0Labels = mixedMoment B raw40328step1 raw40328step1Labels := by
      have ha : raw40328step1 = (fun i j => raw40328step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40328step1 raw40328step0; decide +kernel
      have hl : raw40328step1Labels = raw40328step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40328step0 raw40328step0Labels permutation32 permutation3
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw40329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40329 raw40329Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw40329 raw40329Labels = mixedMoment B raw40329step0 raw40329step0Labels := by
      have hz : ∀ j, raw40329 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40329step0 = (fun i j => raw40329 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40329step0 raw40329; decide +kernel
      have hl : raw40329step0Labels = raw40329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40329 raw40329Labels permutation265 hz
    mixedMoment B raw40329step0 raw40329step0Labels = mixedMoment B raw40329step1 raw40329step1Labels := by
      have ha : raw40329step1 = (fun i j => raw40329step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40329step1 raw40329step0; decide +kernel
      have hl : raw40329step1Labels = raw40329step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40329step0 raw40329step0Labels permutation32 permutation3
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw40330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40330 raw40330Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw40330 raw40330Labels = mixedMoment B raw40330step0 raw40330step0Labels := by
      have hz : ∀ j, raw40330 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40330step0 = (fun i j => raw40330 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40330step0 raw40330; decide +kernel
      have hl : raw40330step0Labels = raw40330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40330 raw40330Labels permutation265 hz
    mixedMoment B raw40330step0 raw40330step0Labels = mixedMoment B raw40330step1 raw40330step1Labels := by
      have ha : raw40330step1 = (fun i j => raw40330step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40330step1 raw40330step0; decide +kernel
      have hl : raw40330step1Labels = raw40330step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40330step0 raw40330step0Labels permutation32 permutation3
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw40331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40331 raw40331Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw40331 raw40331Labels = mixedMoment B raw40331step0 raw40331step0Labels := by
      have hz : ∀ j, raw40331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40331step0 = (fun i j => raw40331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40331step0 raw40331; decide +kernel
      have hl : raw40331step0Labels = raw40331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40331 raw40331Labels permutation265 hz
    mixedMoment B raw40331step0 raw40331step0Labels = mixedMoment B raw40331step1 raw40331step1Labels := by
      have ha : raw40331step1 = (fun i j => raw40331step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40331step1 raw40331step0; decide +kernel
      have hl : raw40331step1Labels = raw40331step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40331step0 raw40331step0Labels permutation32 permutation3
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw40332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40332 raw40332Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw40332 raw40332Labels = mixedMoment B raw40332step0 raw40332step0Labels := by
      have hz : ∀ j, raw40332 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40332step0 = (fun i j => raw40332 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40332step0 raw40332; decide +kernel
      have hl : raw40332step0Labels = raw40332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40332 raw40332Labels permutation265 hz
    mixedMoment B raw40332step0 raw40332step0Labels = mixedMoment B raw40332step1 raw40332step1Labels := by
      have ha : raw40332step1 = (fun i j => raw40332step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40332step1 raw40332step0; decide +kernel
      have hl : raw40332step1Labels = raw40332step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40332step0 raw40332step0Labels permutation32 permutation3
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw40333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40333 raw40333Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw40333 raw40333Labels = mixedMoment B raw40333step0 raw40333step0Labels := by
      have ha : raw40333step0 = (fun i j => raw40333 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40333step0 raw40333; decide +kernel
      have hl : raw40333step0Labels = raw40333Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40333 raw40333Labels permutation152 permutation3
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw40334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40334step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw40334step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40334step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw40334step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40334step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw40334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40334step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw40334step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40334 raw40334Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw40334 raw40334Labels = mixedMoment B raw40334step0 raw40334step0Labels := by
      have hz : ∀ j, raw40334 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40334step0 = (fun i j => raw40334 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40334step0 raw40334; decide +kernel
      have hl : raw40334step0Labels = raw40334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40334 raw40334Labels permutation520 hz
    mixedMoment B raw40334step0 raw40334step0Labels = mixedMoment B raw40334step1 raw40334step1Labels := by
      have hz : ∀ j, raw40334step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40334step1 = (fun i j => raw40334step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40334step1 raw40334step0; decide +kernel
      have hl : raw40334step1Labels = raw40334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40334step0 raw40334step0Labels permutation104 hz
    mixedMoment B raw40334step1 raw40334step1Labels = mixedMoment B raw40334step2 raw40334step2Labels := by
      have hz : ∀ j, raw40334step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40334step2 = (fun i j => raw40334step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40334step2 raw40334step1; decide +kernel
      have hl : raw40334step2Labels = raw40334step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40334step1 raw40334step1Labels permutation20 hz
    mixedMoment B raw40334step2 raw40334step2Labels = mixedMoment B raw40334step3 raw40334step3Labels := by
      have ha : raw40334step3 = (fun i j => raw40334step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40334step3 raw40334step2; decide +kernel
      have hl : raw40334step3Labels = raw40334step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40334step2 raw40334step2Labels permutation7 permutation3
    mixedMoment B raw40334step3 raw40334step3Labels = mixedMoment B raw40334step4 raw40334step4Labels := by
      have ha : raw40334step4 = -raw40334step3 := by apply Matrix.ext; change ∀ i j, raw40334step4 i j = -(raw40334step3 i j); unfold raw40334step4 raw40334step3; decide +kernel
      have hl : raw40334step4Labels = raw40334step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw40335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw40335step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw40335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40335step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw40335step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40335 raw40335Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw40335 raw40335Labels = mixedMoment B raw40335step0 raw40335step0Labels := by
      have hz : ∀ j, raw40335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40335step0 = (fun i j => raw40335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40335step0 raw40335; decide +kernel
      have hl : raw40335step0Labels = raw40335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40335 raw40335Labels permutation434 hz
    mixedMoment B raw40335step0 raw40335step0Labels = mixedMoment B raw40335step1 raw40335step1Labels := by
      have hz : ∀ j, raw40335step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40335step1 = (fun i j => raw40335step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40335step1 raw40335step0; decide +kernel
      have hl : raw40335step1Labels = raw40335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40335step0 raw40335step0Labels permutation80 hz
    mixedMoment B raw40335step1 raw40335step1Labels = mixedMoment B raw40335step2 raw40335step2Labels := by
      have ha : raw40335step2 = (fun i j => raw40335step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40335step2 raw40335step1; decide +kernel
      have hl : raw40335step2Labels = raw40335step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40335step1 raw40335step1Labels permutation31 permutation3
    mixedMoment B raw40335step2 raw40335step2Labels = mixedMoment B raw40335step3 raw40335step3Labels := by
      have ha : raw40335step3 = -raw40335step2 := by apply Matrix.ext; change ∀ i j, raw40335step3 i j = -(raw40335step2 i j); unfold raw40335step3 raw40335step2; decide +kernel
      have hl : raw40335step3Labels = raw40335step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw40336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![3, -1, -2]]
def raw40336step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw40336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40336 raw40336Labels = mixedMoment B node3046 node3046Labels := by
  calc
    mixedMoment B raw40336 raw40336Labels = mixedMoment B raw40336step0 raw40336step0Labels := by
      have hz : ∀ j, raw40336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40336step0 = (fun i j => raw40336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40336step0 raw40336; decide +kernel
      have hl : raw40336step0Labels = raw40336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40336 raw40336Labels permutation434 hz
    mixedMoment B raw40336step0 raw40336step0Labels = mixedMoment B raw40336step1 raw40336step1Labels := by
      have hz : ∀ j, raw40336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40336step1 = (fun i j => raw40336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40336step1 raw40336step0; decide +kernel
      have hl : raw40336step1Labels = raw40336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40336step0 raw40336step0Labels permutation80 hz
    mixedMoment B raw40336step1 raw40336step1Labels = mixedMoment B raw40336step2 raw40336step2Labels := by
      have ha : raw40336step2 = (fun i j => raw40336step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40336step2 raw40336step1; decide +kernel
      have hl : raw40336step2Labels = raw40336step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40336step1 raw40336step1Labels permutation8 permutation3
    _ = mixedMoment B node3046 node3046Labels := by rfl

def raw40337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw40337step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40337 raw40337Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw40337 raw40337Labels = mixedMoment B raw40337step0 raw40337step0Labels := by
      have hz : ∀ j, raw40337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40337step0 = (fun i j => raw40337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40337step0 raw40337; decide +kernel
      have hl : raw40337step0Labels = raw40337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40337 raw40337Labels permutation434 hz
    mixedMoment B raw40337step0 raw40337step0Labels = mixedMoment B raw40337step1 raw40337step1Labels := by
      have hz : ∀ j, raw40337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40337step1 = (fun i j => raw40337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40337step1 raw40337step0; decide +kernel
      have hl : raw40337step1Labels = raw40337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40337step0 raw40337step0Labels permutation80 hz
    mixedMoment B raw40337step1 raw40337step1Labels = mixedMoment B raw40337step2 raw40337step2Labels := by
      have ha : raw40337step2 = (fun i j => raw40337step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40337step2 raw40337step1; decide +kernel
      have hl : raw40337step2Labels = raw40337step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40337step1 raw40337step1Labels permutation8 permutation3
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw40338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw40338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40338 raw40338Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw40338 raw40338Labels = mixedMoment B raw40338step0 raw40338step0Labels := by
      have hz : ∀ j, raw40338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40338step0 = (fun i j => raw40338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40338step0 raw40338; decide +kernel
      have hl : raw40338step0Labels = raw40338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40338 raw40338Labels permutation434 hz
    mixedMoment B raw40338step0 raw40338step0Labels = mixedMoment B raw40338step1 raw40338step1Labels := by
      have hz : ∀ j, raw40338step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40338step1 = (fun i j => raw40338step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40338step1 raw40338step0; decide +kernel
      have hl : raw40338step1Labels = raw40338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40338step0 raw40338step0Labels permutation80 hz
    mixedMoment B raw40338step1 raw40338step1Labels = mixedMoment B raw40338step2 raw40338step2Labels := by
      have ha : raw40338step2 = (fun i j => raw40338step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40338step2 raw40338step1; decide +kernel
      have hl : raw40338step2Labels = raw40338step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40338step1 raw40338step1Labels permutation8 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw40339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40339step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40339step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40339 raw40339Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw40339 raw40339Labels = mixedMoment B raw40339step0 raw40339step0Labels := by
      have hz : ∀ j, raw40339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40339step0 = (fun i j => raw40339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40339step0 raw40339; decide +kernel
      have hl : raw40339step0Labels = raw40339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40339 raw40339Labels permutation434 hz
    mixedMoment B raw40339step0 raw40339step0Labels = mixedMoment B raw40339step1 raw40339step1Labels := by
      have hz : ∀ j, raw40339step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40339step1 = (fun i j => raw40339step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40339step1 raw40339step0; decide +kernel
      have hl : raw40339step1Labels = raw40339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40339step0 raw40339step0Labels permutation80 hz
    mixedMoment B raw40339step1 raw40339step1Labels = mixedMoment B raw40339step2 raw40339step2Labels := by
      have ha : raw40339step2 = (fun i j => raw40339step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40339step2 raw40339step1; decide +kernel
      have hl : raw40339step2Labels = raw40339step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40339step1 raw40339step1Labels permutation8 permutation3
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw40340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw40340step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw40340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40340 raw40340Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw40340 raw40340Labels = mixedMoment B raw40340step0 raw40340step0Labels := by
      have hz : ∀ j, raw40340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40340step0 = (fun i j => raw40340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40340step0 raw40340; decide +kernel
      have hl : raw40340step0Labels = raw40340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40340 raw40340Labels permutation434 hz
    mixedMoment B raw40340step0 raw40340step0Labels = mixedMoment B raw40340step1 raw40340step1Labels := by
      have hz : ∀ j, raw40340step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40340step1 = (fun i j => raw40340step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40340step1 raw40340step0; decide +kernel
      have hl : raw40340step1Labels = raw40340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40340step0 raw40340step0Labels permutation80 hz
    mixedMoment B raw40340step1 raw40340step1Labels = mixedMoment B raw40340step2 raw40340step2Labels := by
      have ha : raw40340step2 = (fun i j => raw40340step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40340step2 raw40340step1; decide +kernel
      have hl : raw40340step2Labels = raw40340step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40340step1 raw40340step1Labels permutation8 permutation3
    _ = mixedMoment B node3056 node3056Labels := by rfl

def raw40341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40341 raw40341Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw40341 raw40341Labels = mixedMoment B raw40341step0 raw40341step0Labels := by
      have hz : ∀ j, raw40341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40341step0 = (fun i j => raw40341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40341step0 raw40341; decide +kernel
      have hl : raw40341step0Labels = raw40341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40341 raw40341Labels permutation346 hz
    mixedMoment B raw40341step0 raw40341step0Labels = mixedMoment B raw40341step1 raw40341step1Labels := by
      have ha : raw40341step1 = (fun i j => raw40341step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40341step1 raw40341step0; decide +kernel
      have hl : raw40341step1Labels = raw40341step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40341step0 raw40341step0Labels permutation32 permutation3
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw40342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40342 raw40342Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw40342 raw40342Labels = mixedMoment B raw40342step0 raw40342step0Labels := by
      have hz : ∀ j, raw40342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40342step0 = (fun i j => raw40342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40342step0 raw40342; decide +kernel
      have hl : raw40342step0Labels = raw40342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40342 raw40342Labels permutation346 hz
    mixedMoment B raw40342step0 raw40342step0Labels = mixedMoment B raw40342step1 raw40342step1Labels := by
      have ha : raw40342step1 = (fun i j => raw40342step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40342step1 raw40342step0; decide +kernel
      have hl : raw40342step1Labels = raw40342step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40342step0 raw40342step0Labels permutation32 permutation3
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw40343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40343step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40343 raw40343Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw40343 raw40343Labels = mixedMoment B raw40343step0 raw40343step0Labels := by
      have hz : ∀ j, raw40343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40343step0 = (fun i j => raw40343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40343step0 raw40343; decide +kernel
      have hl : raw40343step0Labels = raw40343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40343 raw40343Labels permutation346 hz
    mixedMoment B raw40343step0 raw40343step0Labels = mixedMoment B raw40343step1 raw40343step1Labels := by
      have ha : raw40343step1 = (fun i j => raw40343step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40343step1 raw40343step0; decide +kernel
      have hl : raw40343step1Labels = raw40343step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40343step0 raw40343step0Labels permutation32 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw40344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40344 raw40344Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw40344 raw40344Labels = mixedMoment B raw40344step0 raw40344step0Labels := by
      have hz : ∀ j, raw40344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40344step0 = (fun i j => raw40344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40344step0 raw40344; decide +kernel
      have hl : raw40344step0Labels = raw40344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40344 raw40344Labels permutation346 hz
    mixedMoment B raw40344step0 raw40344step0Labels = mixedMoment B raw40344step1 raw40344step1Labels := by
      have ha : raw40344step1 = (fun i j => raw40344step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40344step1 raw40344step0; decide +kernel
      have hl : raw40344step1Labels = raw40344step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40344step0 raw40344step0Labels permutation32 permutation3
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw40345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40345step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40345 raw40345Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw40345 raw40345Labels = mixedMoment B raw40345step0 raw40345step0Labels := by
      have hz : ∀ j, raw40345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40345step0 = (fun i j => raw40345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40345step0 raw40345; decide +kernel
      have hl : raw40345step0Labels = raw40345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40345 raw40345Labels permutation346 hz
    mixedMoment B raw40345step0 raw40345step0Labels = mixedMoment B raw40345step1 raw40345step1Labels := by
      have ha : raw40345step1 = (fun i j => raw40345step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40345step1 raw40345step0; decide +kernel
      have hl : raw40345step1Labels = raw40345step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40345step0 raw40345step0Labels permutation32 permutation3
    _ = mixedMoment B node3044 node3044Labels := by rfl

def raw40346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40346step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40346 raw40346Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw40346 raw40346Labels = mixedMoment B raw40346step0 raw40346step0Labels := by
      have hz : ∀ j, raw40346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40346step0 = (fun i j => raw40346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40346step0 raw40346; decide +kernel
      have hl : raw40346step0Labels = raw40346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40346 raw40346Labels permutation346 hz
    mixedMoment B raw40346step0 raw40346step0Labels = mixedMoment B raw40346step1 raw40346step1Labels := by
      have ha : raw40346step1 = (fun i j => raw40346step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40346step1 raw40346step0; decide +kernel
      have hl : raw40346step1Labels = raw40346step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40346step0 raw40346step0Labels permutation32 permutation3
    _ = mixedMoment B node3045 node3045Labels := by rfl

def raw40347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40347step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw40347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40347 raw40347Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw40347 raw40347Labels = mixedMoment B raw40347step0 raw40347step0Labels := by
      have hz : ∀ j, raw40347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40347step0 = (fun i j => raw40347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40347step0 raw40347; decide +kernel
      have hl : raw40347step0Labels = raw40347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40347 raw40347Labels permutation346 hz
    mixedMoment B raw40347step0 raw40347step0Labels = mixedMoment B raw40347step1 raw40347step1Labels := by
      have ha : raw40347step1 = (fun i j => raw40347step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40347step1 raw40347step0; decide +kernel
      have hl : raw40347step1Labels = raw40347step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40347step0 raw40347step0Labels permutation32 permutation3
    _ = mixedMoment B node3050 node3050Labels := by rfl

def raw40348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40348 raw40348Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw40348 raw40348Labels = mixedMoment B raw40348step0 raw40348step0Labels := by
      have hz : ∀ j, raw40348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40348step0 = (fun i j => raw40348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40348step0 raw40348; decide +kernel
      have hl : raw40348step0Labels = raw40348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40348 raw40348Labels permutation346 hz
    mixedMoment B raw40348step0 raw40348step0Labels = mixedMoment B raw40348step1 raw40348step1Labels := by
      have ha : raw40348step1 = (fun i j => raw40348step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40348step1 raw40348step0; decide +kernel
      have hl : raw40348step1Labels = raw40348step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40348step0 raw40348step0Labels permutation32 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw40349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40349 raw40349Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw40349 raw40349Labels = mixedMoment B raw40349step0 raw40349step0Labels := by
      have hz : ∀ j, raw40349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40349step0 = (fun i j => raw40349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40349step0 raw40349; decide +kernel
      have hl : raw40349step0Labels = raw40349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40349 raw40349Labels permutation346 hz
    mixedMoment B raw40349step0 raw40349step0Labels = mixedMoment B raw40349step1 raw40349step1Labels := by
      have ha : raw40349step1 = (fun i j => raw40349step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40349step1 raw40349step0; decide +kernel
      have hl : raw40349step1Labels = raw40349step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40349step0 raw40349step0Labels permutation32 permutation3
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw40350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40350 raw40350Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw40350 raw40350Labels = mixedMoment B raw40350step0 raw40350step0Labels := by
      have ha : raw40350step0 = (fun i j => raw40350 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40350step0 raw40350; decide +kernel
      have hl : raw40350step0Labels = raw40350Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40350 raw40350Labels permutation152 permutation3
    _ = mixedMoment B node3029 node3029Labels := by rfl

def raw40351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40351 raw40351Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw40351 raw40351Labels = mixedMoment B raw40351step0 raw40351step0Labels := by
      have ha : raw40351step0 = (fun i j => raw40351 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40351step0 raw40351; decide +kernel
      have hl : raw40351step0Labels = raw40351Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40351 raw40351Labels permutation152 permutation3
    _ = mixedMoment B node3030 node3030Labels := by rfl

def raw40352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40352 raw40352Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw40352 raw40352Labels = mixedMoment B raw40352step0 raw40352step0Labels := by
      have ha : raw40352step0 = (fun i j => raw40352 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40352step0 raw40352; decide +kernel
      have hl : raw40352step0Labels = raw40352Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40352 raw40352Labels permutation152 permutation3
    _ = mixedMoment B node3036 node3036Labels := by rfl

def raw40353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40353 raw40353Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw40353 raw40353Labels = mixedMoment B raw40353step0 raw40353step0Labels := by
      have ha : raw40353step0 = (fun i j => raw40353 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40353step0 raw40353; decide +kernel
      have hl : raw40353step0Labels = raw40353Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40353 raw40353Labels permutation152 permutation3
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw40354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40354 raw40354Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw40354 raw40354Labels = mixedMoment B raw40354step0 raw40354step0Labels := by
      have ha : raw40354step0 = (fun i j => raw40354 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40354step0 raw40354; decide +kernel
      have hl : raw40354step0Labels = raw40354Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40354 raw40354Labels permutation152 permutation3
    _ = mixedMoment B node3043 node3043Labels := by rfl

def raw40355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40355step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw40355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40355 raw40355Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw40355 raw40355Labels = mixedMoment B raw40355step0 raw40355step0Labels := by
      have hz : ∀ j, raw40355 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40355step0 = (fun i j => raw40355 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40355step0 raw40355; decide +kernel
      have hl : raw40355step0Labels = raw40355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40355 raw40355Labels permutation520 hz
    mixedMoment B raw40355step0 raw40355step0Labels = mixedMoment B raw40355step1 raw40355step1Labels := by
      have hz : ∀ j, raw40355step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40355step1 = (fun i j => raw40355step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40355step1 raw40355step0; decide +kernel
      have hl : raw40355step1Labels = raw40355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40355step0 raw40355step0Labels permutation104 hz
    mixedMoment B raw40355step1 raw40355step1Labels = mixedMoment B raw40355step2 raw40355step2Labels := by
      have ha : raw40355step2 = (fun i j => raw40355step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40355step2 raw40355step1; decide +kernel
      have hl : raw40355step2Labels = raw40355step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40355step1 raw40355step1Labels permutation29 permutation3
    mixedMoment B raw40355step2 raw40355step2Labels = mixedMoment B raw40355step3 raw40355step3Labels := by
      have ha : raw40355step3 = -raw40355step2 := by apply Matrix.ext; change ∀ i j, raw40355step3 i j = -(raw40355step2 i j); unfold raw40355step3 raw40355step2; decide +kernel
      have hl : raw40355step3Labels = raw40355step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw40356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40356 raw40356Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw40356 raw40356Labels = mixedMoment B raw40356step0 raw40356step0Labels := by
      have hz : ∀ j, raw40356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40356step0 = (fun i j => raw40356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40356step0 raw40356; decide +kernel
      have hl : raw40356step0Labels = raw40356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40356 raw40356Labels permutation434 hz
    mixedMoment B raw40356step0 raw40356step0Labels = mixedMoment B raw40356step1 raw40356step1Labels := by
      have ha : raw40356step1 = (fun i j => raw40356step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40356step1 raw40356step0; decide +kernel
      have hl : raw40356step1Labels = raw40356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40356step0 raw40356step0Labels permutation32 permutation3
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw40357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40357 raw40357Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw40357 raw40357Labels = mixedMoment B raw40357step0 raw40357step0Labels := by
      have hz : ∀ j, raw40357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40357step0 = (fun i j => raw40357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40357step0 raw40357; decide +kernel
      have hl : raw40357step0Labels = raw40357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40357 raw40357Labels permutation434 hz
    mixedMoment B raw40357step0 raw40357step0Labels = mixedMoment B raw40357step1 raw40357step1Labels := by
      have ha : raw40357step1 = (fun i j => raw40357step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40357step1 raw40357step0; decide +kernel
      have hl : raw40357step1Labels = raw40357step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40357step0 raw40357step0Labels permutation32 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw40358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40358 raw40358Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw40358 raw40358Labels = mixedMoment B raw40358step0 raw40358step0Labels := by
      have hz : ∀ j, raw40358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40358step0 = (fun i j => raw40358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40358step0 raw40358; decide +kernel
      have hl : raw40358step0Labels = raw40358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40358 raw40358Labels permutation434 hz
    mixedMoment B raw40358step0 raw40358step0Labels = mixedMoment B raw40358step1 raw40358step1Labels := by
      have ha : raw40358step1 = (fun i j => raw40358step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40358step1 raw40358step0; decide +kernel
      have hl : raw40358step1Labels = raw40358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40358step0 raw40358step0Labels permutation32 permutation3
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw40359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40359 raw40359Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw40359 raw40359Labels = mixedMoment B raw40359step0 raw40359step0Labels := by
      have ha : raw40359step0 = (fun i j => raw40359 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40359step0 raw40359; decide +kernel
      have hl : raw40359step0Labels = raw40359Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40359 raw40359Labels permutation152 permutation3
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw40360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40360 raw40360Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw40360 raw40360Labels = mixedMoment B raw40360step0 raw40360step0Labels := by
      have ha : raw40360step0 = (fun i j => raw40360 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40360step0 raw40360; decide +kernel
      have hl : raw40360step0Labels = raw40360Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40360 raw40360Labels permutation152 permutation3
    _ = mixedMoment B node3066 node3066Labels := by rfl

def raw40361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40361 raw40361Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw40361 raw40361Labels = mixedMoment B raw40361step0 raw40361step0Labels := by
      have ha : raw40361step0 = (fun i j => raw40361 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40361step0 raw40361; decide +kernel
      have hl : raw40361step0Labels = raw40361Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40361 raw40361Labels permutation152 permutation3
    _ = mixedMoment B node3068 node3068Labels := by rfl

def raw40362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40362 raw40362Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw40362 raw40362Labels = mixedMoment B raw40362step0 raw40362step0Labels := by
      have ha : raw40362step0 = (fun i j => raw40362 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40362step0 raw40362; decide +kernel
      have hl : raw40362step0Labels = raw40362Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40362 raw40362Labels permutation152 permutation3
    _ = mixedMoment B node3069 node3069Labels := by rfl

def raw40363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw40363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40363 raw40363Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw40363 raw40363Labels = mixedMoment B raw40363step0 raw40363step0Labels := by
      have ha : raw40363step0 = (fun i j => raw40363 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40363step0 raw40363; decide +kernel
      have hl : raw40363step0Labels = raw40363Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40363 raw40363Labels permutation152 permutation3
    _ = mixedMoment B node3073 node3073Labels := by rfl

def raw40364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40364 raw40364Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw40364 raw40364Labels = mixedMoment B raw40364step0 raw40364step0Labels := by
      have ha : raw40364step0 = (fun i j => raw40364 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40364step0 raw40364; decide +kernel
      have hl : raw40364step0Labels = raw40364Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40364 raw40364Labels permutation152 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw40365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40365 raw40365Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw40365 raw40365Labels = mixedMoment B raw40365step0 raw40365step0Labels := by
      have hz : ∀ j, raw40365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40365step0 = (fun i j => raw40365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40365step0 raw40365; decide +kernel
      have hl : raw40365step0Labels = raw40365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40365 raw40365Labels permutation434 hz
    mixedMoment B raw40365step0 raw40365step0Labels = mixedMoment B raw40365step1 raw40365step1Labels := by
      have hz : ∀ j, raw40365step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40365step1 = (fun i j => raw40365step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40365step1 raw40365step0; decide +kernel
      have hl : raw40365step1Labels = raw40365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40365step0 raw40365step0Labels permutation80 hz
    mixedMoment B raw40365step1 raw40365step1Labels = mixedMoment B raw40365step2 raw40365step2Labels := by
      have ha : raw40365step2 = (fun i j => raw40365step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40365step2 raw40365step1; decide +kernel
      have hl : raw40365step2Labels = raw40365step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40365step1 raw40365step1Labels permutation8 permutation3
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw40366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40366step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw40366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40366 raw40366Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw40366 raw40366Labels = mixedMoment B raw40366step0 raw40366step0Labels := by
      have hz : ∀ j, raw40366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40366step0 = (fun i j => raw40366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40366step0 raw40366; decide +kernel
      have hl : raw40366step0Labels = raw40366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40366 raw40366Labels permutation434 hz
    mixedMoment B raw40366step0 raw40366step0Labels = mixedMoment B raw40366step1 raw40366step1Labels := by
      have hz : ∀ j, raw40366step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40366step1 = (fun i j => raw40366step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40366step1 raw40366step0; decide +kernel
      have hl : raw40366step1Labels = raw40366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40366step0 raw40366step0Labels permutation80 hz
    mixedMoment B raw40366step1 raw40366step1Labels = mixedMoment B raw40366step2 raw40366step2Labels := by
      have ha : raw40366step2 = (fun i j => raw40366step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40366step2 raw40366step1; decide +kernel
      have hl : raw40366step2Labels = raw40366step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40366step1 raw40366step1Labels permutation28 permutation6
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw40367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40367 raw40367Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw40367 raw40367Labels = mixedMoment B raw40367step0 raw40367step0Labels := by
      have hz : ∀ j, raw40367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40367step0 = (fun i j => raw40367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40367step0 raw40367; decide +kernel
      have hl : raw40367step0Labels = raw40367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40367 raw40367Labels permutation346 hz
    mixedMoment B raw40367step0 raw40367step0Labels = mixedMoment B raw40367step1 raw40367step1Labels := by
      have ha : raw40367step1 = (fun i j => raw40367step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40367step1 raw40367step0; decide +kernel
      have hl : raw40367step1Labels = raw40367step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40367step0 raw40367step0Labels permutation32 permutation3
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw40368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40368 raw40368Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw40368 raw40368Labels = mixedMoment B raw40368step0 raw40368step0Labels := by
      have hz : ∀ j, raw40368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40368step0 = (fun i j => raw40368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40368step0 raw40368; decide +kernel
      have hl : raw40368step0Labels = raw40368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40368 raw40368Labels permutation346 hz
    mixedMoment B raw40368step0 raw40368step0Labels = mixedMoment B raw40368step1 raw40368step1Labels := by
      have ha : raw40368step1 = (fun i j => raw40368step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40368step1 raw40368step0; decide +kernel
      have hl : raw40368step1Labels = raw40368step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40368step0 raw40368step0Labels permutation137 permutation6
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw40369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw40369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40369 raw40369Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw40369 raw40369Labels = mixedMoment B raw40369step0 raw40369step0Labels := by
      have hz : ∀ j, raw40369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40369step0 = (fun i j => raw40369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40369step0 raw40369; decide +kernel
      have hl : raw40369step0Labels = raw40369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40369 raw40369Labels permutation346 hz
    mixedMoment B raw40369step0 raw40369step0Labels = mixedMoment B raw40369step1 raw40369step1Labels := by
      have ha : raw40369step1 = (fun i j => raw40369step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40369step1 raw40369step0; decide +kernel
      have hl : raw40369step1Labels = raw40369step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40369step0 raw40369step0Labels permutation32 permutation3
    _ = mixedMoment B node3096 node3096Labels := by rfl

def raw40370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40370 raw40370Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw40370 raw40370Labels = mixedMoment B raw40370step0 raw40370step0Labels := by
      have hz : ∀ j, raw40370 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40370step0 = (fun i j => raw40370 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40370step0 raw40370; decide +kernel
      have hl : raw40370step0Labels = raw40370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40370 raw40370Labels permutation346 hz
    mixedMoment B raw40370step0 raw40370step0Labels = mixedMoment B raw40370step1 raw40370step1Labels := by
      have ha : raw40370step1 = (fun i j => raw40370step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40370step1 raw40370step0; decide +kernel
      have hl : raw40370step1Labels = raw40370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40370step0 raw40370step0Labels permutation32 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw40371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40371 raw40371Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw40371 raw40371Labels = mixedMoment B raw40371step0 raw40371step0Labels := by
      have ha : raw40371step0 = (fun i j => raw40371 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40371step0 raw40371; decide +kernel
      have hl : raw40371step0Labels = raw40371Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40371 raw40371Labels permutation152 permutation3
    _ = mixedMoment B node3084 node3084Labels := by rfl

def raw40372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40372step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40372step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw40372step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40372step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw40372step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40372 raw40372Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw40372 raw40372Labels = mixedMoment B raw40372step0 raw40372step0Labels := by
      have hz : ∀ j, raw40372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40372step0 = (fun i j => raw40372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40372step0 raw40372; decide +kernel
      have hl : raw40372step0Labels = raw40372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40372 raw40372Labels permutation434 hz
    mixedMoment B raw40372step0 raw40372step0Labels = mixedMoment B raw40372step1 raw40372step1Labels := by
      have hz : ∀ j, raw40372step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40372step1 = (fun i j => raw40372step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40372step1 raw40372step0; decide +kernel
      have hl : raw40372step1Labels = raw40372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40372step0 raw40372step0Labels permutation80 hz
    mixedMoment B raw40372step1 raw40372step1Labels = mixedMoment B raw40372step2 raw40372step2Labels := by
      have hz : ∀ j, raw40372step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40372step2 = (fun i j => raw40372step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40372step2 raw40372step1; decide +kernel
      have hl : raw40372step2Labels = raw40372step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40372step1 raw40372step1Labels permutation14 hz
    mixedMoment B raw40372step2 raw40372step2Labels = mixedMoment B raw40372step3 raw40372step3Labels := by
      have ha : raw40372step3 = (fun i j => raw40372step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40372step3 raw40372step2; decide +kernel
      have hl : raw40372step3Labels = raw40372step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40372step2 raw40372step2Labels permutation5 permutation6
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw40373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40373step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40373step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw40373step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40373step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw40373step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40373 raw40373Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw40373 raw40373Labels = mixedMoment B raw40373step0 raw40373step0Labels := by
      have hz : ∀ j, raw40373 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40373step0 = (fun i j => raw40373 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40373step0 raw40373; decide +kernel
      have hl : raw40373step0Labels = raw40373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40373 raw40373Labels permutation434 hz
    mixedMoment B raw40373step0 raw40373step0Labels = mixedMoment B raw40373step1 raw40373step1Labels := by
      have hz : ∀ j, raw40373step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40373step1 = (fun i j => raw40373step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40373step1 raw40373step0; decide +kernel
      have hl : raw40373step1Labels = raw40373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40373step0 raw40373step0Labels permutation80 hz
    mixedMoment B raw40373step1 raw40373step1Labels = mixedMoment B raw40373step2 raw40373step2Labels := by
      have hz : ∀ j, raw40373step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40373step2 = (fun i j => raw40373step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40373step2 raw40373step1; decide +kernel
      have hl : raw40373step2Labels = raw40373step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40373step1 raw40373step1Labels permutation14 hz
    mixedMoment B raw40373step2 raw40373step2Labels = mixedMoment B raw40373step3 raw40373step3Labels := by
      have ha : raw40373step3 = (fun i j => raw40373step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40373step3 raw40373step2; decide +kernel
      have hl : raw40373step3Labels = raw40373step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40373step2 raw40373step2Labels permutation6 permutation6
    _ = mixedMoment B node1310 node1310Labels := by rfl

def raw40374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw40374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40374 raw40374Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw40374 raw40374Labels = mixedMoment B raw40374step0 raw40374step0Labels := by
      have hz : ∀ j, raw40374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40374step0 = (fun i j => raw40374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40374step0 raw40374; decide +kernel
      have hl : raw40374step0Labels = raw40374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40374 raw40374Labels permutation346 hz
    mixedMoment B raw40374step0 raw40374step0Labels = mixedMoment B raw40374step1 raw40374step1Labels := by
      have hz : ∀ j, raw40374step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40374step1 = (fun i j => raw40374step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40374step1 raw40374step0; decide +kernel
      have hl : raw40374step1Labels = raw40374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40374step0 raw40374step0Labels permutation56 hz
    mixedMoment B raw40374step1 raw40374step1Labels = mixedMoment B raw40374step2 raw40374step2Labels := by
      have ha : raw40374step2 = (fun i j => raw40374step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40374step2 raw40374step1; decide +kernel
      have hl : raw40374step2Labels = raw40374step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40374step1 raw40374step1Labels permutation25 permutation6
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw40375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40375 raw40375Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw40375 raw40375Labels = mixedMoment B raw40375step0 raw40375step0Labels := by
      have hz : ∀ j, raw40375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40375step0 = (fun i j => raw40375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40375step0 raw40375; decide +kernel
      have hl : raw40375step0Labels = raw40375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40375 raw40375Labels permutation346 hz
    mixedMoment B raw40375step0 raw40375step0Labels = mixedMoment B raw40375step1 raw40375step1Labels := by
      have hz : ∀ j, raw40375step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40375step1 = (fun i j => raw40375step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40375step1 raw40375step0; decide +kernel
      have hl : raw40375step1Labels = raw40375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40375step0 raw40375step0Labels permutation56 hz
    mixedMoment B raw40375step1 raw40375step1Labels = mixedMoment B raw40375step2 raw40375step2Labels := by
      have ha : raw40375step2 = (fun i j => raw40375step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40375step2 raw40375step1; decide +kernel
      have hl : raw40375step2Labels = raw40375step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40375step1 raw40375step1Labels permutation29 permutation6
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw40376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40376step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40376 raw40376Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw40376 raw40376Labels = mixedMoment B raw40376step0 raw40376step0Labels := by
      have hz : ∀ j, raw40376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40376step0 = (fun i j => raw40376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40376step0 raw40376; decide +kernel
      have hl : raw40376step0Labels = raw40376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40376 raw40376Labels permutation346 hz
    mixedMoment B raw40376step0 raw40376step0Labels = mixedMoment B raw40376step1 raw40376step1Labels := by
      have hz : ∀ j, raw40376step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40376step1 = (fun i j => raw40376step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40376step1 raw40376step0; decide +kernel
      have hl : raw40376step1Labels = raw40376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40376step0 raw40376step0Labels permutation56 hz
    mixedMoment B raw40376step1 raw40376step1Labels = mixedMoment B raw40376step2 raw40376step2Labels := by
      have ha : raw40376step2 = (fun i j => raw40376step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40376step2 raw40376step1; decide +kernel
      have hl : raw40376step2Labels = raw40376step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40376step1 raw40376step1Labels permutation24 permutation6
    _ = mixedMoment B node2643 node2643Labels := by rfl

def raw40377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40377step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40377step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40377 raw40377Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw40377 raw40377Labels = mixedMoment B raw40377step0 raw40377step0Labels := by
      have hz : ∀ j, raw40377 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40377step0 = (fun i j => raw40377 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40377step0 raw40377; decide +kernel
      have hl : raw40377step0Labels = raw40377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40377 raw40377Labels permutation346 hz
    mixedMoment B raw40377step0 raw40377step0Labels = mixedMoment B raw40377step1 raw40377step1Labels := by
      have hz : ∀ j, raw40377step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40377step1 = (fun i j => raw40377step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40377step1 raw40377step0; decide +kernel
      have hl : raw40377step1Labels = raw40377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40377step0 raw40377step0Labels permutation56 hz
    mixedMoment B raw40377step1 raw40377step1Labels = mixedMoment B raw40377step2 raw40377step2Labels := by
      have ha : raw40377step2 = (fun i j => raw40377step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40377step2 raw40377step1; decide +kernel
      have hl : raw40377step2Labels = raw40377step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40377step1 raw40377step1Labels permutation30 permutation6
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw40378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw40378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw40378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw40378step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40378step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw40378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40378 raw40378Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw40378 raw40378Labels = mixedMoment B raw40378step0 raw40378step0Labels := by
      have hz : ∀ j, raw40378 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40378step0 = (fun i j => raw40378 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40378step0 raw40378; decide +kernel
      have hl : raw40378step0Labels = raw40378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40378 raw40378Labels permutation346 hz
    mixedMoment B raw40378step0 raw40378step0Labels = mixedMoment B raw40378step1 raw40378step1Labels := by
      have hz : ∀ j, raw40378step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40378step1 = (fun i j => raw40378step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40378step1 raw40378step0; decide +kernel
      have hl : raw40378step1Labels = raw40378step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40378step0 raw40378step0Labels permutation56 hz
    mixedMoment B raw40378step1 raw40378step1Labels = mixedMoment B raw40378step2 raw40378step2Labels := by
      have ha : raw40378step2 = (fun i j => raw40378step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40378step2 raw40378step1; decide +kernel
      have hl : raw40378step2Labels = raw40378step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40378step1 raw40378step1Labels permutation16 permutation6
    _ = mixedMoment B node2603 node2603Labels := by rfl

def raw40379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40379step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40379 raw40379Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw40379 raw40379Labels = mixedMoment B raw40379step0 raw40379step0Labels := by
      have hz : ∀ j, raw40379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40379step0 = (fun i j => raw40379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40379step0 raw40379; decide +kernel
      have hl : raw40379step0Labels = raw40379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40379 raw40379Labels permutation346 hz
    mixedMoment B raw40379step0 raw40379step0Labels = mixedMoment B raw40379step1 raw40379step1Labels := by
      have hz : ∀ j, raw40379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40379step1 = (fun i j => raw40379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40379step1 raw40379step0; decide +kernel
      have hl : raw40379step1Labels = raw40379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40379step0 raw40379step0Labels permutation56 hz
    mixedMoment B raw40379step1 raw40379step1Labels = mixedMoment B raw40379step2 raw40379step2Labels := by
      have ha : raw40379step2 = (fun i j => raw40379step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40379step2 raw40379step1; decide +kernel
      have hl : raw40379step2Labels = raw40379step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40379step1 raw40379step1Labels permutation17 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw40380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40380step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw40380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40380 raw40380Labels = mixedMoment B node3118 node3118Labels := by
  calc
    mixedMoment B raw40380 raw40380Labels = mixedMoment B raw40380step0 raw40380step0Labels := by
      have hz : ∀ j, raw40380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40380step0 = (fun i j => raw40380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40380step0 raw40380; decide +kernel
      have hl : raw40380step0Labels = raw40380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40380 raw40380Labels permutation346 hz
    mixedMoment B raw40380step0 raw40380step0Labels = mixedMoment B raw40380step1 raw40380step1Labels := by
      have hz : ∀ j, raw40380step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40380step1 = (fun i j => raw40380step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40380step1 raw40380step0; decide +kernel
      have hl : raw40380step1Labels = raw40380step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40380step0 raw40380step0Labels permutation56 hz
    mixedMoment B raw40380step1 raw40380step1Labels = mixedMoment B raw40380step2 raw40380step2Labels := by
      have ha : raw40380step2 = (fun i j => raw40380step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40380step2 raw40380step1; decide +kernel
      have hl : raw40380step2Labels = raw40380step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40380step1 raw40380step1Labels permutation8 permutation3
    _ = mixedMoment B node3118 node3118Labels := by rfl

def raw40381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40381 raw40381Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw40381 raw40381Labels = mixedMoment B raw40381step0 raw40381step0Labels := by
      have hz : ∀ j, raw40381 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40381step0 = (fun i j => raw40381 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40381step0 raw40381; decide +kernel
      have hl : raw40381step0Labels = raw40381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40381 raw40381Labels permutation265 hz
    mixedMoment B raw40381step0 raw40381step0Labels = mixedMoment B raw40381step1 raw40381step1Labels := by
      have ha : raw40381step1 = (fun i j => raw40381step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40381step1 raw40381step0; decide +kernel
      have hl : raw40381step1Labels = raw40381step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40381step0 raw40381step0Labels permutation125 permutation6
    _ = mixedMoment B node2641 node2641Labels := by rfl

def raw40382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40382 raw40382Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw40382 raw40382Labels = mixedMoment B raw40382step0 raw40382step0Labels := by
      have hz : ∀ j, raw40382 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40382step0 = (fun i j => raw40382 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40382step0 raw40382; decide +kernel
      have hl : raw40382step0Labels = raw40382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40382 raw40382Labels permutation265 hz
    mixedMoment B raw40382step0 raw40382step0Labels = mixedMoment B raw40382step1 raw40382step1Labels := by
      have ha : raw40382step1 = (fun i j => raw40382step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40382step1 raw40382step0; decide +kernel
      have hl : raw40382step1Labels = raw40382step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40382step0 raw40382step0Labels permutation149 permutation6
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw40383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40383 raw40383Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw40383 raw40383Labels = mixedMoment B raw40383step0 raw40383step0Labels := by
      have hz : ∀ j, raw40383 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40383step0 = (fun i j => raw40383 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40383step0 raw40383; decide +kernel
      have hl : raw40383step0Labels = raw40383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40383 raw40383Labels permutation265 hz
    mixedMoment B raw40383step0 raw40383step0Labels = mixedMoment B raw40383step1 raw40383step1Labels := by
      have ha : raw40383step1 = (fun i j => raw40383step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40383step1 raw40383step0; decide +kernel
      have hl : raw40383step1Labels = raw40383step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40383step0 raw40383step0Labels permutation95 permutation6
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw40384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40384 raw40384Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw40384 raw40384Labels = mixedMoment B raw40384step0 raw40384step0Labels := by
      have hz : ∀ j, raw40384 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40384step0 = (fun i j => raw40384 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40384step0 raw40384; decide +kernel
      have hl : raw40384step0Labels = raw40384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40384 raw40384Labels permutation265 hz
    mixedMoment B raw40384step0 raw40384step0Labels = mixedMoment B raw40384step1 raw40384step1Labels := by
      have ha : raw40384step1 = (fun i j => raw40384step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40384step1 raw40384step0; decide +kernel
      have hl : raw40384step1Labels = raw40384step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40384step0 raw40384step0Labels permutation97 permutation6
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw40385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw40385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40385 raw40385Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw40385 raw40385Labels = mixedMoment B raw40385step0 raw40385step0Labels := by
      have hz : ∀ j, raw40385 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40385step0 = (fun i j => raw40385 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40385step0 raw40385; decide +kernel
      have hl : raw40385step0Labels = raw40385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40385 raw40385Labels permutation265 hz
    mixedMoment B raw40385step0 raw40385step0Labels = mixedMoment B raw40385step1 raw40385step1Labels := by
      have ha : raw40385step1 = (fun i j => raw40385step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40385step1 raw40385step0; decide +kernel
      have hl : raw40385step1Labels = raw40385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40385step0 raw40385step0Labels permutation32 permutation3
    _ = mixedMoment B node3108 node3108Labels := by rfl

def raw40386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40386 raw40386Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw40386 raw40386Labels = mixedMoment B raw40386step0 raw40386step0Labels := by
      have hz : ∀ j, raw40386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40386step0 = (fun i j => raw40386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40386step0 raw40386; decide +kernel
      have hl : raw40386step0Labels = raw40386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40386 raw40386Labels permutation265 hz
    mixedMoment B raw40386step0 raw40386step0Labels = mixedMoment B raw40386step1 raw40386step1Labels := by
      have ha : raw40386step1 = (fun i j => raw40386step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40386step1 raw40386step0; decide +kernel
      have hl : raw40386step1Labels = raw40386step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40386step0 raw40386step0Labels permutation96 permutation6
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw40387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40387 raw40387Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw40387 raw40387Labels = mixedMoment B raw40387step0 raw40387step0Labels := by
      have ha : raw40387step0 = (fun i j => raw40387 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40387step0 raw40387; decide +kernel
      have hl : raw40387step0Labels = raw40387Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40387 raw40387Labels permutation502 permutation6
    _ = mixedMoment B node2573 node2573Labels := by rfl

def raw40388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw40388step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40388step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw40388step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40388step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-3, 3, 0]]
def raw40388step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40388step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw40388step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40388 raw40388Labels = mixedMoment B node2285 node2285Labels := by
  calc
    mixedMoment B raw40388 raw40388Labels = mixedMoment B raw40388step0 raw40388step0Labels := by
      have hz : ∀ j, raw40388 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40388step0 = (fun i j => raw40388 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40388step0 raw40388; decide +kernel
      have hl : raw40388step0Labels = raw40388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40388 raw40388Labels permutation520 hz
    mixedMoment B raw40388step0 raw40388step0Labels = mixedMoment B raw40388step1 raw40388step1Labels := by
      have hz : ∀ j, raw40388step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40388step1 = (fun i j => raw40388step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40388step1 raw40388step0; decide +kernel
      have hl : raw40388step1Labels = raw40388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40388step0 raw40388step0Labels permutation104 hz
    mixedMoment B raw40388step1 raw40388step1Labels = mixedMoment B raw40388step2 raw40388step2Labels := by
      have hz : ∀ j, raw40388step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40388step2 = (fun i j => raw40388step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40388step2 raw40388step1; decide +kernel
      have hl : raw40388step2Labels = raw40388step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40388step1 raw40388step1Labels permutation20 hz
    mixedMoment B raw40388step2 raw40388step2Labels = mixedMoment B raw40388step3 raw40388step3Labels := by
      have ha : raw40388step3 = (fun i j => raw40388step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40388step3 raw40388step2; decide +kernel
      have hl : raw40388step3Labels = raw40388step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40388step2 raw40388step2Labels permutation7 permutation3
    mixedMoment B raw40388step3 raw40388step3Labels = mixedMoment B raw40388step4 raw40388step4Labels := by
      have ha : raw40388step4 = -raw40388step3 := by apply Matrix.ext; change ∀ i j, raw40388step4 i j = -(raw40388step3 i j); unfold raw40388step4 raw40388step3; decide +kernel
      have hl : raw40388step4Labels = raw40388step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2285 node2285Labels := by rfl

def raw40389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![3, -2, -1]]
def raw40389step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw40389step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40389 raw40389Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw40389 raw40389Labels = mixedMoment B raw40389step0 raw40389step0Labels := by
      have hz : ∀ j, raw40389 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40389step0 = (fun i j => raw40389 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40389step0 raw40389; decide +kernel
      have hl : raw40389step0Labels = raw40389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40389 raw40389Labels permutation434 hz
    mixedMoment B raw40389step0 raw40389step0Labels = mixedMoment B raw40389step1 raw40389step1Labels := by
      have hz : ∀ j, raw40389step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40389step1 = (fun i j => raw40389step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40389step1 raw40389step0; decide +kernel
      have hl : raw40389step1Labels = raw40389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40389step0 raw40389step0Labels permutation80 hz
    mixedMoment B raw40389step1 raw40389step1Labels = mixedMoment B raw40389step2 raw40389step2Labels := by
      have ha : raw40389step2 = (fun i j => raw40389step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40389step2 raw40389step1; decide +kernel
      have hl : raw40389step2Labels = raw40389step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40389step1 raw40389step1Labels permutation19 permutation6
    _ = mixedMoment B node2136 node2136Labels := by rfl

def raw40390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![3, -1, -2]]
def raw40390step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40390 raw40390Labels = mixedMoment B node1832 node1832Labels := by
  calc
    mixedMoment B raw40390 raw40390Labels = mixedMoment B raw40390step0 raw40390step0Labels := by
      have hz : ∀ j, raw40390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40390step0 = (fun i j => raw40390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40390step0 raw40390; decide +kernel
      have hl : raw40390step0Labels = raw40390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40390 raw40390Labels permutation434 hz
    mixedMoment B raw40390step0 raw40390step0Labels = mixedMoment B raw40390step1 raw40390step1Labels := by
      have hz : ∀ j, raw40390step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40390step1 = (fun i j => raw40390step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40390step1 raw40390step0; decide +kernel
      have hl : raw40390step1Labels = raw40390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40390step0 raw40390step0Labels permutation80 hz
    mixedMoment B raw40390step1 raw40390step1Labels = mixedMoment B raw40390step2 raw40390step2Labels := by
      have ha : raw40390step2 = (fun i j => raw40390step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40390step2 raw40390step1; decide +kernel
      have hl : raw40390step2Labels = raw40390step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40390step1 raw40390step1Labels permutation19 permutation6
    _ = mixedMoment B node1832 node1832Labels := by rfl

def raw40391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw40391step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw40391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40391 raw40391Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw40391 raw40391Labels = mixedMoment B raw40391step0 raw40391step0Labels := by
      have hz : ∀ j, raw40391 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40391step0 = (fun i j => raw40391 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40391step0 raw40391; decide +kernel
      have hl : raw40391step0Labels = raw40391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40391 raw40391Labels permutation434 hz
    mixedMoment B raw40391step0 raw40391step0Labels = mixedMoment B raw40391step1 raw40391step1Labels := by
      have hz : ∀ j, raw40391step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40391step1 = (fun i j => raw40391step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40391step1 raw40391step0; decide +kernel
      have hl : raw40391step1Labels = raw40391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40391step0 raw40391step0Labels permutation80 hz
    mixedMoment B raw40391step1 raw40391step1Labels = mixedMoment B raw40391step2 raw40391step2Labels := by
      have ha : raw40391step2 = (fun i j => raw40391step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40391step2 raw40391step1; decide +kernel
      have hl : raw40391step2Labels = raw40391step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40391step1 raw40391step1Labels permutation17 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw40392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw40392step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40392 raw40392Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw40392 raw40392Labels = mixedMoment B raw40392step0 raw40392step0Labels := by
      have hz : ∀ j, raw40392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40392step0 = (fun i j => raw40392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40392step0 raw40392; decide +kernel
      have hl : raw40392step0Labels = raw40392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40392 raw40392Labels permutation434 hz
    mixedMoment B raw40392step0 raw40392step0Labels = mixedMoment B raw40392step1 raw40392step1Labels := by
      have hz : ∀ j, raw40392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40392step1 = (fun i j => raw40392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40392step1 raw40392step0; decide +kernel
      have hl : raw40392step1Labels = raw40392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40392step0 raw40392step0Labels permutation80 hz
    mixedMoment B raw40392step1 raw40392step1Labels = mixedMoment B raw40392step2 raw40392step2Labels := by
      have ha : raw40392step2 = (fun i j => raw40392step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40392step2 raw40392step1; decide +kernel
      have hl : raw40392step2Labels = raw40392step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40392step1 raw40392step1Labels permutation19 permutation6
    _ = mixedMoment B node2113 node2113Labels := by rfl

def raw40393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw40393step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw40393step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40393 raw40393Labels = mixedMoment B node1820 node1820Labels := by
  calc
    mixedMoment B raw40393 raw40393Labels = mixedMoment B raw40393step0 raw40393step0Labels := by
      have hz : ∀ j, raw40393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40393step0 = (fun i j => raw40393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40393step0 raw40393; decide +kernel
      have hl : raw40393step0Labels = raw40393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40393 raw40393Labels permutation434 hz
    mixedMoment B raw40393step0 raw40393step0Labels = mixedMoment B raw40393step1 raw40393step1Labels := by
      have hz : ∀ j, raw40393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40393step1 = (fun i j => raw40393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40393step1 raw40393step0; decide +kernel
      have hl : raw40393step1Labels = raw40393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40393step0 raw40393step0Labels permutation80 hz
    mixedMoment B raw40393step1 raw40393step1Labels = mixedMoment B raw40393step2 raw40393step2Labels := by
      have ha : raw40393step2 = (fun i j => raw40393step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40393step2 raw40393step1; decide +kernel
      have hl : raw40393step2Labels = raw40393step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40393step1 raw40393step1Labels permutation19 permutation6
    _ = mixedMoment B node1820 node1820Labels := by rfl

def raw40394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40394 raw40394Labels = mixedMoment B node1828 node1828Labels := by
  calc
    mixedMoment B raw40394 raw40394Labels = mixedMoment B raw40394step0 raw40394step0Labels := by
      have hz : ∀ j, raw40394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40394step0 = (fun i j => raw40394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40394step0 raw40394; decide +kernel
      have hl : raw40394step0Labels = raw40394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40394 raw40394Labels permutation346 hz
    mixedMoment B raw40394step0 raw40394step0Labels = mixedMoment B raw40394step1 raw40394step1Labels := by
      have ha : raw40394step1 = (fun i j => raw40394step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40394step1 raw40394step0; decide +kernel
      have hl : raw40394step1Labels = raw40394step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40394step0 raw40394step0Labels permutation77 permutation6
    _ = mixedMoment B node1828 node1828Labels := by rfl

def raw40395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw40395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40395 raw40395Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw40395 raw40395Labels = mixedMoment B raw40395step0 raw40395step0Labels := by
      have hz : ∀ j, raw40395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40395step0 = (fun i j => raw40395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40395step0 raw40395; decide +kernel
      have hl : raw40395step0Labels = raw40395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40395 raw40395Labels permutation346 hz
    mixedMoment B raw40395step0 raw40395step0Labels = mixedMoment B raw40395step1 raw40395step1Labels := by
      have ha : raw40395step1 = (fun i j => raw40395step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40395step1 raw40395step0; decide +kernel
      have hl : raw40395step1Labels = raw40395step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40395step0 raw40395step0Labels permutation73 permutation6
    _ = mixedMoment B node2037 node2037Labels := by rfl

def raw40396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40396 raw40396Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw40396 raw40396Labels = mixedMoment B raw40396step0 raw40396step0Labels := by
      have hz : ∀ j, raw40396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40396step0 = (fun i j => raw40396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40396step0 raw40396; decide +kernel
      have hl : raw40396step0Labels = raw40396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40396 raw40396Labels permutation346 hz
    mixedMoment B raw40396step0 raw40396step0Labels = mixedMoment B raw40396step1 raw40396step1Labels := by
      have ha : raw40396step1 = (fun i j => raw40396step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40396step1 raw40396step0; decide +kernel
      have hl : raw40396step1Labels = raw40396step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40396step0 raw40396step0Labels permutation79 permutation6
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw40397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40397 raw40397Labels = mixedMoment B node1813 node1813Labels := by
  calc
    mixedMoment B raw40397 raw40397Labels = mixedMoment B raw40397step0 raw40397step0Labels := by
      have hz : ∀ j, raw40397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40397step0 = (fun i j => raw40397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40397step0 raw40397; decide +kernel
      have hl : raw40397step0Labels = raw40397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40397 raw40397Labels permutation346 hz
    mixedMoment B raw40397step0 raw40397step0Labels = mixedMoment B raw40397step1 raw40397step1Labels := by
      have ha : raw40397step1 = (fun i j => raw40397step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40397step1 raw40397step0; decide +kernel
      have hl : raw40397step1Labels = raw40397step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40397step0 raw40397step0Labels permutation77 permutation6
    _ = mixedMoment B node1813 node1813Labels := by rfl

def raw40398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40398 raw40398Labels = mixedMoment B node1980 node1980Labels := by
  calc
    mixedMoment B raw40398 raw40398Labels = mixedMoment B raw40398step0 raw40398step0Labels := by
      have hz : ∀ j, raw40398 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40398step0 = (fun i j => raw40398 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40398step0 raw40398; decide +kernel
      have hl : raw40398step0Labels = raw40398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40398 raw40398Labels permutation346 hz
    mixedMoment B raw40398step0 raw40398step0Labels = mixedMoment B raw40398step1 raw40398step1Labels := by
      have ha : raw40398step1 = (fun i j => raw40398step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40398step1 raw40398step0; decide +kernel
      have hl : raw40398step1Labels = raw40398step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40398step0 raw40398step0Labels permutation73 permutation6
    _ = mixedMoment B node1980 node1980Labels := by rfl

def raw40399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40399 raw40399Labels = mixedMoment B node1797 node1797Labels := by
  calc
    mixedMoment B raw40399 raw40399Labels = mixedMoment B raw40399step0 raw40399step0Labels := by
      have hz : ∀ j, raw40399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40399step0 = (fun i j => raw40399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40399step0 raw40399; decide +kernel
      have hl : raw40399step0Labels = raw40399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40399 raw40399Labels permutation346 hz
    mixedMoment B raw40399step0 raw40399step0Labels = mixedMoment B raw40399step1 raw40399step1Labels := by
      have ha : raw40399step1 = (fun i j => raw40399step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40399step1 raw40399step0; decide +kernel
      have hl : raw40399step1Labels = raw40399step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40399step0 raw40399step0Labels permutation79 permutation6
    _ = mixedMoment B node1797 node1797Labels := by rfl

def raw40400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw40400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40400 raw40400Labels = mixedMoment B node1971 node1971Labels := by
  calc
    mixedMoment B raw40400 raw40400Labels = mixedMoment B raw40400step0 raw40400step0Labels := by
      have hz : ∀ j, raw40400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40400step0 = (fun i j => raw40400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40400step0 raw40400; decide +kernel
      have hl : raw40400step0Labels = raw40400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40400 raw40400Labels permutation346 hz
    mixedMoment B raw40400step0 raw40400step0Labels = mixedMoment B raw40400step1 raw40400step1Labels := by
      have ha : raw40400step1 = (fun i j => raw40400step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40400step1 raw40400step0; decide +kernel
      have hl : raw40400step1Labels = raw40400step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40400step0 raw40400step0Labels permutation65 permutation6
    _ = mixedMoment B node1971 node1971Labels := by rfl

def raw40401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40401 raw40401Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw40401 raw40401Labels = mixedMoment B raw40401step0 raw40401step0Labels := by
      have hz : ∀ j, raw40401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40401step0 = (fun i j => raw40401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40401step0 raw40401; decide +kernel
      have hl : raw40401step0Labels = raw40401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40401 raw40401Labels permutation346 hz
    mixedMoment B raw40401step0 raw40401step0Labels = mixedMoment B raw40401step1 raw40401step1Labels := by
      have ha : raw40401step1 = (fun i j => raw40401step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40401step1 raw40401step0; decide +kernel
      have hl : raw40401step1Labels = raw40401step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40401step0 raw40401step0Labels permutation65 permutation6
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw40402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40402 raw40402Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw40402 raw40402Labels = mixedMoment B raw40402step0 raw40402step0Labels := by
      have hz : ∀ j, raw40402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40402step0 = (fun i j => raw40402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40402step0 raw40402; decide +kernel
      have hl : raw40402step0Labels = raw40402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40402 raw40402Labels permutation346 hz
    mixedMoment B raw40402step0 raw40402step0Labels = mixedMoment B raw40402step1 raw40402step1Labels := by
      have ha : raw40402step1 = (fun i j => raw40402step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40402step1 raw40402step0; decide +kernel
      have hl : raw40402step1Labels = raw40402step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40402step0 raw40402step0Labels permutation65 permutation6
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw40403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40403 raw40403Labels = mixedMoment B node1976 node1976Labels := by
  calc
    mixedMoment B raw40403 raw40403Labels = mixedMoment B raw40403step0 raw40403step0Labels := by
      have ha : raw40403step0 = (fun i j => raw40403 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40403step0 raw40403; decide +kernel
      have hl : raw40403step0Labels = raw40403Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40403 raw40403Labels permutation332 permutation6
    _ = mixedMoment B node1976 node1976Labels := by rfl

def raw40404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40404 raw40404Labels = mixedMoment B node1793 node1793Labels := by
  calc
    mixedMoment B raw40404 raw40404Labels = mixedMoment B raw40404step0 raw40404step0Labels := by
      have ha : raw40404step0 = (fun i j => raw40404 (permutation345 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40404step0 raw40404; decide +kernel
      have hl : raw40404step0Labels = raw40404Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40404 raw40404Labels permutation345 permutation6
    _ = mixedMoment B node1793 node1793Labels := by rfl

def raw40405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40405 raw40405Labels = mixedMoment B node1965 node1965Labels := by
  calc
    mixedMoment B raw40405 raw40405Labels = mixedMoment B raw40405step0 raw40405step0Labels := by
      have ha : raw40405step0 = (fun i j => raw40405 (permutation316 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40405step0 raw40405; decide +kernel
      have hl : raw40405step0Labels = raw40405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40405 raw40405Labels permutation316 permutation6
    _ = mixedMoment B node1965 node1965Labels := by rfl

def raw40406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40406 raw40406Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw40406 raw40406Labels = mixedMoment B raw40406step0 raw40406step0Labels := by
      have ha : raw40406step0 = (fun i j => raw40406 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40406step0 raw40406; decide +kernel
      have hl : raw40406step0Labels = raw40406Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40406 raw40406Labels permutation317 permutation6
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw40407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40407 raw40407Labels = mixedMoment B node1957 node1957Labels := by
  calc
    mixedMoment B raw40407 raw40407Labels = mixedMoment B raw40407step0 raw40407step0Labels := by
      have ha : raw40407step0 = (fun i j => raw40407 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40407step0 raw40407; decide +kernel
      have hl : raw40407step0Labels = raw40407Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40407 raw40407Labels permutation317 permutation6
    _ = mixedMoment B node1957 node1957Labels := by rfl

def raw40408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw40408step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw40408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40408step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw40408step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40408 raw40408Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw40408 raw40408Labels = mixedMoment B raw40408step0 raw40408step0Labels := by
      have hz : ∀ j, raw40408 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40408step0 = (fun i j => raw40408 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40408step0 raw40408; decide +kernel
      have hl : raw40408step0Labels = raw40408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40408 raw40408Labels permutation520 hz
    mixedMoment B raw40408step0 raw40408step0Labels = mixedMoment B raw40408step1 raw40408step1Labels := by
      have hz : ∀ j, raw40408step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40408step1 = (fun i j => raw40408step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40408step1 raw40408step0; decide +kernel
      have hl : raw40408step1Labels = raw40408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40408step0 raw40408step0Labels permutation104 hz
    mixedMoment B raw40408step1 raw40408step1Labels = mixedMoment B raw40408step2 raw40408step2Labels := by
      have ha : raw40408step2 = (fun i j => raw40408step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40408step2 raw40408step1; decide +kernel
      have hl : raw40408step2Labels = raw40408step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40408step1 raw40408step1Labels permutation31 permutation3
    mixedMoment B raw40408step2 raw40408step2Labels = mixedMoment B raw40408step3 raw40408step3Labels := by
      have ha : raw40408step3 = -raw40408step2 := by apply Matrix.ext; change ∀ i j, raw40408step3 i j = -(raw40408step2 i j); unfold raw40408step3 raw40408step2; decide +kernel
      have hl : raw40408step3Labels = raw40408step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw40409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw40409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw40409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40409 raw40409Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw40409 raw40409Labels = mixedMoment B raw40409step0 raw40409step0Labels := by
      have hz : ∀ j, raw40409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40409step0 = (fun i j => raw40409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40409step0 raw40409; decide +kernel
      have hl : raw40409step0Labels = raw40409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40409 raw40409Labels permutation434 hz
    mixedMoment B raw40409step0 raw40409step0Labels = mixedMoment B raw40409step1 raw40409step1Labels := by
      have ha : raw40409step1 = (fun i j => raw40409step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40409step1 raw40409step0; decide +kernel
      have hl : raw40409step1Labels = raw40409step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40409step0 raw40409step0Labels permutation151 permutation3
    mixedMoment B raw40409step1 raw40409step1Labels = mixedMoment B raw40409step2 raw40409step2Labels := by
      have ha : raw40409step2 = -raw40409step1 := by apply Matrix.ext; change ∀ i j, raw40409step2 i j = -(raw40409step1 i j); unfold raw40409step2 raw40409step1; decide +kernel
      have hl : raw40409step2Labels = raw40409step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw40410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw40410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw40410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40410 raw40410Labels = mixedMoment B node3033 node3033Labels := by
  calc
    mixedMoment B raw40410 raw40410Labels = mixedMoment B raw40410step0 raw40410step0Labels := by
      have hz : ∀ j, raw40410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40410step0 = (fun i j => raw40410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40410step0 raw40410; decide +kernel
      have hl : raw40410step0Labels = raw40410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40410 raw40410Labels permutation434 hz
    mixedMoment B raw40410step0 raw40410step0Labels = mixedMoment B raw40410step1 raw40410step1Labels := by
      have ha : raw40410step1 = (fun i j => raw40410step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40410step1 raw40410step0; decide +kernel
      have hl : raw40410step1Labels = raw40410step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40410step0 raw40410step0Labels permutation151 permutation3
    mixedMoment B raw40410step1 raw40410step1Labels = mixedMoment B raw40410step2 raw40410step2Labels := by
      have ha : raw40410step2 = -raw40410step1 := by apply Matrix.ext; change ∀ i j, raw40410step2 i j = -(raw40410step1 i j); unfold raw40410step2 raw40410step1; decide +kernel
      have hl : raw40410step2Labels = raw40410step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3033 node3033Labels := by rfl

def raw40411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40411 raw40411Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw40411 raw40411Labels = mixedMoment B raw40411step0 raw40411step0Labels := by
      have hz : ∀ j, raw40411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40411step0 = (fun i j => raw40411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40411step0 raw40411; decide +kernel
      have hl : raw40411step0Labels = raw40411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40411 raw40411Labels permutation434 hz
    mixedMoment B raw40411step0 raw40411step0Labels = mixedMoment B raw40411step1 raw40411step1Labels := by
      have ha : raw40411step1 = (fun i j => raw40411step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40411step1 raw40411step0; decide +kernel
      have hl : raw40411step1Labels = raw40411step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40411step0 raw40411step0Labels permutation55 permutation6
    mixedMoment B raw40411step1 raw40411step1Labels = mixedMoment B raw40411step2 raw40411step2Labels := by
      have ha : raw40411step2 = -raw40411step1 := by apply Matrix.ext; change ∀ i j, raw40411step2 i j = -(raw40411step1 i j); unfold raw40411step2 raw40411step1; decide +kernel
      have hl : raw40411step2Labels = raw40411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw40412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40412step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40412 raw40412Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw40412 raw40412Labels = mixedMoment B raw40412step0 raw40412step0Labels := by
      have hz : ∀ j, raw40412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40412step0 = (fun i j => raw40412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40412step0 raw40412; decide +kernel
      have hl : raw40412step0Labels = raw40412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40412 raw40412Labels permutation434 hz
    mixedMoment B raw40412step0 raw40412step0Labels = mixedMoment B raw40412step1 raw40412step1Labels := by
      have ha : raw40412step1 = (fun i j => raw40412step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40412step1 raw40412step0; decide +kernel
      have hl : raw40412step1Labels = raw40412step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40412step0 raw40412step0Labels permutation32 permutation3
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw40413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40413 raw40413Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw40413 raw40413Labels = mixedMoment B raw40413step0 raw40413step0Labels := by
      have hz : ∀ j, raw40413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40413step0 = (fun i j => raw40413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40413step0 raw40413; decide +kernel
      have hl : raw40413step0Labels = raw40413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40413 raw40413Labels permutation434 hz
    mixedMoment B raw40413step0 raw40413step0Labels = mixedMoment B raw40413step1 raw40413step1Labels := by
      have ha : raw40413step1 = (fun i j => raw40413step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40413step1 raw40413step0; decide +kernel
      have hl : raw40413step1Labels = raw40413step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40413step0 raw40413step0Labels permutation49 permutation6
    mixedMoment B raw40413step1 raw40413step1Labels = mixedMoment B raw40413step2 raw40413step2Labels := by
      have ha : raw40413step2 = -raw40413step1 := by apply Matrix.ext; change ∀ i j, raw40413step2 i j = -(raw40413step1 i j); unfold raw40413step2 raw40413step1; decide +kernel
      have hl : raw40413step2Labels = raw40413step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw40414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40414 raw40414Labels = mixedMoment B node3131 node3131Labels := by
  calc
    mixedMoment B raw40414 raw40414Labels = mixedMoment B raw40414step0 raw40414step0Labels := by
      have hz : ∀ j, raw40414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40414step0 = (fun i j => raw40414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40414step0 raw40414; decide +kernel
      have hl : raw40414step0Labels = raw40414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40414 raw40414Labels permutation434 hz
    mixedMoment B raw40414step0 raw40414step0Labels = mixedMoment B raw40414step1 raw40414step1Labels := by
      have ha : raw40414step1 = (fun i j => raw40414step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40414step1 raw40414step0; decide +kernel
      have hl : raw40414step1Labels = raw40414step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40414step0 raw40414step0Labels permutation47 permutation6
    mixedMoment B raw40414step1 raw40414step1Labels = mixedMoment B raw40414step2 raw40414step2Labels := by
      have ha : raw40414step2 = -raw40414step1 := by apply Matrix.ext; change ∀ i j, raw40414step2 i j = -(raw40414step1 i j); unfold raw40414step2 raw40414step1; decide +kernel
      have hl : raw40414step2Labels = raw40414step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3131 node3131Labels := by rfl

def raw40415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw40415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw40415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40415 raw40415Labels = mixedMoment B node3062 node3062Labels := by
  calc
    mixedMoment B raw40415 raw40415Labels = mixedMoment B raw40415step0 raw40415step0Labels := by
      have ha : raw40415step0 = (fun i j => raw40415 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40415step0 raw40415; decide +kernel
      have hl : raw40415step0Labels = raw40415Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40415 raw40415Labels permutation664 permutation3
    mixedMoment B raw40415step0 raw40415step0Labels = mixedMoment B raw40415step1 raw40415step1Labels := by
      have ha : raw40415step1 = -raw40415step0 := by apply Matrix.ext; change ∀ i j, raw40415step1 i j = -(raw40415step0 i j); unfold raw40415step1 raw40415step0; decide +kernel
      have hl : raw40415step1Labels = raw40415step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3062 node3062Labels := by rfl

def raw40416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40416 raw40416Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw40416 raw40416Labels = mixedMoment B raw40416step0 raw40416step0Labels := by
      have ha : raw40416step0 = (fun i j => raw40416 (permutation223 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40416step0 raw40416; decide +kernel
      have hl : raw40416step0Labels = raw40416Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40416 raw40416Labels permutation223 permutation6
    mixedMoment B raw40416step0 raw40416step0Labels = mixedMoment B raw40416step1 raw40416step1Labels := by
      have ha : raw40416step1 = -raw40416step0 := by apply Matrix.ext; change ∀ i j, raw40416step1 i j = -(raw40416step0 i j); unfold raw40416step1 raw40416step0; decide +kernel
      have hl : raw40416step1Labels = raw40416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3196 node3196Labels := by rfl

def raw40417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40417 raw40417Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw40417 raw40417Labels = mixedMoment B raw40417step0 raw40417step0Labels := by
      have ha : raw40417step0 = (fun i j => raw40417 (permutation217 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40417step0 raw40417; decide +kernel
      have hl : raw40417step0Labels = raw40417Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40417 raw40417Labels permutation217 permutation6
    mixedMoment B raw40417step0 raw40417step0Labels = mixedMoment B raw40417step1 raw40417step1Labels := by
      have ha : raw40417step1 = -raw40417step0 := by apply Matrix.ext; change ∀ i j, raw40417step1 i j = -(raw40417step0 i j); unfold raw40417step1 raw40417step0; decide +kernel
      have hl : raw40417step1Labels = raw40417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw40418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40418 raw40418Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw40418 raw40418Labels = mixedMoment B raw40418step0 raw40418step0Labels := by
      have ha : raw40418step0 = (fun i j => raw40418 (permutation237 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40418step0 raw40418; decide +kernel
      have hl : raw40418step0Labels = raw40418Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40418 raw40418Labels permutation237 permutation6
    mixedMoment B raw40418step0 raw40418step0Labels = mixedMoment B raw40418step1 raw40418step1Labels := by
      have ha : raw40418step1 = -raw40418step0 := by apply Matrix.ext; change ∀ i j, raw40418step1 i j = -(raw40418step0 i j); unfold raw40418step1 raw40418step0; decide +kernel
      have hl : raw40418step1Labels = raw40418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3163 node3163Labels := by rfl

def raw40419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40419 raw40419Labels = mixedMoment B node3136 node3136Labels := by
  calc
    mixedMoment B raw40419 raw40419Labels = mixedMoment B raw40419step0 raw40419step0Labels := by
      have ha : raw40419step0 = (fun i j => raw40419 (permutation223 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40419step0 raw40419; decide +kernel
      have hl : raw40419step0Labels = raw40419Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40419 raw40419Labels permutation223 permutation6
    mixedMoment B raw40419step0 raw40419step0Labels = mixedMoment B raw40419step1 raw40419step1Labels := by
      have ha : raw40419step1 = -raw40419step0 := by apply Matrix.ext; change ∀ i j, raw40419step1 i j = -(raw40419step0 i j); unfold raw40419step1 raw40419step0; decide +kernel
      have hl : raw40419step1Labels = raw40419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3136 node3136Labels := by rfl

def raw40420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40420 raw40420Labels = mixedMoment B node3134 node3134Labels := by
  calc
    mixedMoment B raw40420 raw40420Labels = mixedMoment B raw40420step0 raw40420step0Labels := by
      have ha : raw40420step0 = (fun i j => raw40420 (permutation215 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40420step0 raw40420; decide +kernel
      have hl : raw40420step0Labels = raw40420Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40420 raw40420Labels permutation215 permutation6
    mixedMoment B raw40420step0 raw40420step0Labels = mixedMoment B raw40420step1 raw40420step1Labels := by
      have ha : raw40420step1 = -raw40420step0 := by apply Matrix.ext; change ∀ i j, raw40420step1 i j = -(raw40420step0 i j); unfold raw40420step1 raw40420step0; decide +kernel
      have hl : raw40420step1Labels = raw40420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3134 node3134Labels := by rfl

def raw40421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40421 raw40421Labels = mixedMoment B node3127 node3127Labels := by
  calc
    mixedMoment B raw40421 raw40421Labels = mixedMoment B raw40421step0 raw40421step0Labels := by
      have ha : raw40421step0 = (fun i j => raw40421 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40421step0 raw40421; decide +kernel
      have hl : raw40421step0Labels = raw40421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40421 raw40421Labels permutation259 permutation6
    mixedMoment B raw40421step0 raw40421step0Labels = mixedMoment B raw40421step1 raw40421step1Labels := by
      have ha : raw40421step1 = -raw40421step0 := by apply Matrix.ext; change ∀ i j, raw40421step1 i j = -(raw40421step0 i j); unfold raw40421step1 raw40421step0; decide +kernel
      have hl : raw40421step1Labels = raw40421step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3127 node3127Labels := by rfl

def raw40422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40422 raw40422Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw40422 raw40422Labels = mixedMoment B raw40422step0 raw40422step0Labels := by
      have ha : raw40422step0 = (fun i j => raw40422 (permutation264 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40422step0 raw40422; decide +kernel
      have hl : raw40422step0Labels = raw40422Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40422 raw40422Labels permutation264 permutation6
    mixedMoment B raw40422step0 raw40422step0Labels = mixedMoment B raw40422step1 raw40422step1Labels := by
      have ha : raw40422step1 = -raw40422step0 := by apply Matrix.ext; change ∀ i j, raw40422step1 i j = -(raw40422step0 i j); unfold raw40422step1 raw40422step0; decide +kernel
      have hl : raw40422step1Labels = raw40422step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw40423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40423 raw40423Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw40423 raw40423Labels = mixedMoment B raw40423step0 raw40423step0Labels := by
      have ha : raw40423step0 = (fun i j => raw40423 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40423step0 raw40423; decide +kernel
      have hl : raw40423step0Labels = raw40423Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40423 raw40423Labels permutation152 permutation3
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw40424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40424step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw40424step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40424step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw40424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40424step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw40424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40424 raw40424Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw40424 raw40424Labels = mixedMoment B raw40424step0 raw40424step0Labels := by
      have hz : ∀ j, raw40424 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40424step0 = (fun i j => raw40424 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40424step0 raw40424; decide +kernel
      have hl : raw40424step0Labels = raw40424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40424 raw40424Labels permutation434 hz
    mixedMoment B raw40424step0 raw40424step0Labels = mixedMoment B raw40424step1 raw40424step1Labels := by
      have hz : ∀ j, raw40424step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40424step1 = (fun i j => raw40424step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40424step1 raw40424step0; decide +kernel
      have hl : raw40424step1Labels = raw40424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40424step0 raw40424step0Labels permutation80 hz
    mixedMoment B raw40424step1 raw40424step1Labels = mixedMoment B raw40424step2 raw40424step2Labels := by
      have ha : raw40424step2 = (fun i j => raw40424step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40424step2 raw40424step1; decide +kernel
      have hl : raw40424step2Labels = raw40424step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40424step1 raw40424step1Labels permutation13 permutation6
    mixedMoment B raw40424step2 raw40424step2Labels = mixedMoment B raw40424step3 raw40424step3Labels := by
      have ha : raw40424step3 = -raw40424step2 := by apply Matrix.ext; change ∀ i j, raw40424step3 i j = -(raw40424step2 i j); unfold raw40424step3 raw40424step2; decide +kernel
      have hl : raw40424step3Labels = raw40424step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3161 node3161Labels := by rfl

def raw40425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40425step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw40425step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw40425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40425 raw40425Labels = mixedMoment B node2821 node2821Labels := by
  calc
    mixedMoment B raw40425 raw40425Labels = mixedMoment B raw40425step0 raw40425step0Labels := by
      have hz : ∀ j, raw40425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40425step0 = (fun i j => raw40425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40425step0 raw40425; decide +kernel
      have hl : raw40425step0Labels = raw40425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40425 raw40425Labels permutation434 hz
    mixedMoment B raw40425step0 raw40425step0Labels = mixedMoment B raw40425step1 raw40425step1Labels := by
      have hz : ∀ j, raw40425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40425step1 = (fun i j => raw40425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40425step1 raw40425step0; decide +kernel
      have hl : raw40425step1Labels = raw40425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40425step0 raw40425step0Labels permutation80 hz
    mixedMoment B raw40425step1 raw40425step1Labels = mixedMoment B raw40425step2 raw40425step2Labels := by
      have ha : raw40425step2 = (fun i j => raw40425step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40425step2 raw40425step1; decide +kernel
      have hl : raw40425step2Labels = raw40425step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40425step1 raw40425step1Labels permutation29 permutation6
    _ = mixedMoment B node2821 node2821Labels := by rfl

def raw40426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40426step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw40426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw40426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40426 raw40426Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw40426 raw40426Labels = mixedMoment B raw40426step0 raw40426step0Labels := by
      have hz : ∀ j, raw40426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40426step0 = (fun i j => raw40426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40426step0 raw40426; decide +kernel
      have hl : raw40426step0Labels = raw40426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40426 raw40426Labels permutation346 hz
    mixedMoment B raw40426step0 raw40426step0Labels = mixedMoment B raw40426step1 raw40426step1Labels := by
      have ha : raw40426step1 = (fun i j => raw40426step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40426step1 raw40426step0; decide +kernel
      have hl : raw40426step1Labels = raw40426step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40426step0 raw40426step0Labels permutation43 permutation6
    mixedMoment B raw40426step1 raw40426step1Labels = mixedMoment B raw40426step2 raw40426step2Labels := by
      have ha : raw40426step2 = -raw40426step1 := by apply Matrix.ext; change ∀ i j, raw40426step2 i j = -(raw40426step1 i j); unfold raw40426step2 raw40426step1; decide +kernel
      have hl : raw40426step2Labels = raw40426step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3198 node3198Labels := by rfl

def raw40427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40427step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40427 raw40427Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw40427 raw40427Labels = mixedMoment B raw40427step0 raw40427step0Labels := by
      have hz : ∀ j, raw40427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40427step0 = (fun i j => raw40427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40427step0 raw40427; decide +kernel
      have hl : raw40427step0Labels = raw40427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40427 raw40427Labels permutation346 hz
    mixedMoment B raw40427step0 raw40427step0Labels = mixedMoment B raw40427step1 raw40427step1Labels := by
      have ha : raw40427step1 = (fun i j => raw40427step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40427step1 raw40427step0; decide +kernel
      have hl : raw40427step1Labels = raw40427step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40427step0 raw40427step0Labels permutation137 permutation6
    _ = mixedMoment B node2816 node2816Labels := by rfl

def raw40428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40428step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40428 raw40428Labels = mixedMoment B node3138 node3138Labels := by
  calc
    mixedMoment B raw40428 raw40428Labels = mixedMoment B raw40428step0 raw40428step0Labels := by
      have hz : ∀ j, raw40428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40428step0 = (fun i j => raw40428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40428step0 raw40428; decide +kernel
      have hl : raw40428step0Labels = raw40428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40428 raw40428Labels permutation346 hz
    mixedMoment B raw40428step0 raw40428step0Labels = mixedMoment B raw40428step1 raw40428step1Labels := by
      have ha : raw40428step1 = (fun i j => raw40428step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40428step1 raw40428step0; decide +kernel
      have hl : raw40428step1Labels = raw40428step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40428step0 raw40428step0Labels permutation43 permutation6
    mixedMoment B raw40428step1 raw40428step1Labels = mixedMoment B raw40428step2 raw40428step2Labels := by
      have ha : raw40428step2 = -raw40428step1 := by apply Matrix.ext; change ∀ i j, raw40428step2 i j = -(raw40428step1 i j); unfold raw40428step2 raw40428step1; decide +kernel
      have hl : raw40428step2Labels = raw40428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3138 node3138Labels := by rfl

def raw40429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40429step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40429 raw40429Labels = mixedMoment B node2803 node2803Labels := by
  calc
    mixedMoment B raw40429 raw40429Labels = mixedMoment B raw40429step0 raw40429step0Labels := by
      have hz : ∀ j, raw40429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40429step0 = (fun i j => raw40429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40429step0 raw40429; decide +kernel
      have hl : raw40429step0Labels = raw40429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40429 raw40429Labels permutation346 hz
    mixedMoment B raw40429step0 raw40429step0Labels = mixedMoment B raw40429step1 raw40429step1Labels := by
      have ha : raw40429step1 = (fun i j => raw40429step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40429step1 raw40429step0; decide +kernel
      have hl : raw40429step1Labels = raw40429step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40429step0 raw40429step0Labels permutation139 permutation6
    _ = mixedMoment B node2803 node2803Labels := by rfl

def raw40430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40430step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40430 raw40430Labels = mixedMoment B node3129 node3129Labels := by
  calc
    mixedMoment B raw40430 raw40430Labels = mixedMoment B raw40430step0 raw40430step0Labels := by
      have hz : ∀ j, raw40430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40430step0 = (fun i j => raw40430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40430step0 raw40430; decide +kernel
      have hl : raw40430step0Labels = raw40430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40430 raw40430Labels permutation346 hz
    mixedMoment B raw40430step0 raw40430step0Labels = mixedMoment B raw40430step1 raw40430step1Labels := by
      have ha : raw40430step1 = (fun i j => raw40430step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40430step1 raw40430step0; decide +kernel
      have hl : raw40430step1Labels = raw40430step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40430step0 raw40430step0Labels permutation55 permutation6
    mixedMoment B raw40430step1 raw40430step1Labels = mixedMoment B raw40430step2 raw40430step2Labels := by
      have ha : raw40430step2 = -raw40430step1 := by apply Matrix.ext; change ∀ i j, raw40430step2 i j = -(raw40430step1 i j); unfold raw40430step2 raw40430step1; decide +kernel
      have hl : raw40430step2Labels = raw40430step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3129 node3129Labels := by rfl

def raw40431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40431step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40431 raw40431Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw40431 raw40431Labels = mixedMoment B raw40431step0 raw40431step0Labels := by
      have hz : ∀ j, raw40431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40431step0 = (fun i j => raw40431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40431step0 raw40431; decide +kernel
      have hl : raw40431step0Labels = raw40431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40431 raw40431Labels permutation346 hz
    mixedMoment B raw40431step0 raw40431step0Labels = mixedMoment B raw40431step1 raw40431step1Labels := by
      have ha : raw40431step1 = (fun i j => raw40431step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40431step1 raw40431step0; decide +kernel
      have hl : raw40431step1Labels = raw40431step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40431step0 raw40431step0Labels permutation55 permutation6
    mixedMoment B raw40431step1 raw40431step1Labels = mixedMoment B raw40431step2 raw40431step2Labels := by
      have ha : raw40431step2 = -raw40431step1 := by apply Matrix.ext; change ∀ i j, raw40431step2 i j = -(raw40431step1 i j); unfold raw40431step2 raw40431step1; decide +kernel
      have hl : raw40431step2Labels = raw40431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3174 node3174Labels := by rfl

def raw40432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40432 raw40432Labels = mixedMoment B node3189 node3189Labels := by
  calc
    mixedMoment B raw40432 raw40432Labels = mixedMoment B raw40432step0 raw40432step0Labels := by
      have ha : raw40432step0 = (fun i j => raw40432 (permutation187 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40432step0 raw40432; decide +kernel
      have hl : raw40432step0Labels = raw40432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40432 raw40432Labels permutation187 permutation6
    mixedMoment B raw40432step0 raw40432step0Labels = mixedMoment B raw40432step1 raw40432step1Labels := by
      have ha : raw40432step1 = -raw40432step0 := by apply Matrix.ext; change ∀ i j, raw40432step1 i j = -(raw40432step0 i j); unfold raw40432step1 raw40432step0; decide +kernel
      have hl : raw40432step1Labels = raw40432step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3189 node3189Labels := by rfl

def raw40433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40433 raw40433Labels = mixedMoment B node2800 node2800Labels := by
  calc
    mixedMoment B raw40433 raw40433Labels = mixedMoment B raw40433step0 raw40433step0Labels := by
      have ha : raw40433step0 = (fun i j => raw40433 (permutation620 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40433step0 raw40433; decide +kernel
      have hl : raw40433step0Labels = raw40433Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40433 raw40433Labels permutation620 permutation6
    _ = mixedMoment B node2800 node2800Labels := by rfl

def raw40434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40434 raw40434Labels = mixedMoment B node3162 node3162Labels := by
  calc
    mixedMoment B raw40434 raw40434Labels = mixedMoment B raw40434step0 raw40434step0Labels := by
      have ha : raw40434step0 = (fun i j => raw40434 (permutation256 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40434step0 raw40434; decide +kernel
      have hl : raw40434step0Labels = raw40434Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40434 raw40434Labels permutation256 permutation6
    mixedMoment B raw40434step0 raw40434step0Labels = mixedMoment B raw40434step1 raw40434step1Labels := by
      have ha : raw40434step1 = -raw40434step0 := by apply Matrix.ext; change ∀ i j, raw40434step1 i j = -(raw40434step0 i j); unfold raw40434step1 raw40434step0; decide +kernel
      have hl : raw40434step1Labels = raw40434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3162 node3162Labels := by rfl

def raw40435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40435 raw40435Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw40435 raw40435Labels = mixedMoment B raw40435step0 raw40435step0Labels := by
      have ha : raw40435step0 = (fun i j => raw40435 (permutation193 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40435step0 raw40435; decide +kernel
      have hl : raw40435step0Labels = raw40435Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40435 raw40435Labels permutation193 permutation6
    mixedMoment B raw40435step0 raw40435step0Labels = mixedMoment B raw40435step1 raw40435step1Labels := by
      have ha : raw40435step1 = -raw40435step0 := by apply Matrix.ext; change ∀ i j, raw40435step1 i j = -(raw40435step0 i j); unfold raw40435step1 raw40435step0; decide +kernel
      have hl : raw40435step1Labels = raw40435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw40436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40436 raw40436Labels = mixedMoment B node3133 node3133Labels := by
  calc
    mixedMoment B raw40436 raw40436Labels = mixedMoment B raw40436step0 raw40436step0Labels := by
      have ha : raw40436step0 = (fun i j => raw40436 (permutation199 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40436step0 raw40436; decide +kernel
      have hl : raw40436step0Labels = raw40436Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40436 raw40436Labels permutation199 permutation6
    mixedMoment B raw40436step0 raw40436step0Labels = mixedMoment B raw40436step1 raw40436step1Labels := by
      have ha : raw40436step1 = -raw40436step0 := by apply Matrix.ext; change ∀ i j, raw40436step1 i j = -(raw40436step0 i j); unfold raw40436step1 raw40436step0; decide +kernel
      have hl : raw40436step1Labels = raw40436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3133 node3133Labels := by rfl

def raw40437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40437Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw40437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40437 raw40437Labels = mixedMoment B node2707 node2707Labels := by
  calc
    mixedMoment B raw40437 raw40437Labels = mixedMoment B raw40437step0 raw40437step0Labels := by
      have ha : raw40437step0 = (fun i j => raw40437 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40437step0 raw40437; decide +kernel
      have hl : raw40437step0Labels = raw40437Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40437 raw40437Labels permutation674 permutation3
    mixedMoment B raw40437step0 raw40437step0Labels = mixedMoment B raw40437step1 raw40437step1Labels := by
      have ha : raw40437step1 = -raw40437step0 := by apply Matrix.ext; change ∀ i j, raw40437step1 i j = -(raw40437step0 i j); unfold raw40437step1 raw40437step0; decide +kernel
      have hl : raw40437step1Labels = raw40437step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2707 node2707Labels := by rfl

def raw40438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40438Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40438 raw40438Labels = mixedMoment B node3155 node3155Labels := by
  calc
    mixedMoment B raw40438 raw40438Labels = mixedMoment B raw40438step0 raw40438step0Labels := by
      have ha : raw40438step0 = (fun i j => raw40438 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40438step0 raw40438; decide +kernel
      have hl : raw40438step0Labels = raw40438Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40438 raw40438Labels permutation260 permutation6
    mixedMoment B raw40438step0 raw40438step0Labels = mixedMoment B raw40438step1 raw40438step1Labels := by
      have ha : raw40438step1 = -raw40438step0 := by apply Matrix.ext; change ∀ i j, raw40438step1 i j = -(raw40438step0 i j); unfold raw40438step1 raw40438step0; decide +kernel
      have hl : raw40438step1Labels = raw40438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3155 node3155Labels := by rfl

def raw40439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40439 raw40439Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw40439 raw40439Labels = mixedMoment B raw40439step0 raw40439step0Labels := by
      have ha : raw40439step0 = (fun i j => raw40439 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40439step0 raw40439; decide +kernel
      have hl : raw40439step0Labels = raw40439Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40439 raw40439Labels permutation260 permutation6
    mixedMoment B raw40439step0 raw40439step0Labels = mixedMoment B raw40439step1 raw40439step1Labels := by
      have ha : raw40439step1 = -raw40439step0 := by apply Matrix.ext; change ∀ i j, raw40439step1 i j = -(raw40439step0 i j); unfold raw40439step1 raw40439step0; decide +kernel
      have hl : raw40439step1Labels = raw40439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw40440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40440 raw40440Labels = mixedMoment B node3179 node3179Labels := by
  calc
    mixedMoment B raw40440 raw40440Labels = mixedMoment B raw40440step0 raw40440step0Labels := by
      have ha : raw40440step0 = (fun i j => raw40440 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40440step0 raw40440; decide +kernel
      have hl : raw40440step0Labels = raw40440Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40440 raw40440Labels permutation240 permutation6
    mixedMoment B raw40440step0 raw40440step0Labels = mixedMoment B raw40440step1 raw40440step1Labels := by
      have ha : raw40440step1 = -raw40440step0 := by apply Matrix.ext; change ∀ i j, raw40440step1 i j = -(raw40440step0 i j); unfold raw40440step1 raw40440step0; decide +kernel
      have hl : raw40440step1Labels = raw40440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3179 node3179Labels := by rfl

def raw40441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40441 raw40441Labels = mixedMoment B node3130 node3130Labels := by
  calc
    mixedMoment B raw40441 raw40441Labels = mixedMoment B raw40441step0 raw40441step0Labels := by
      have ha : raw40441step0 = (fun i j => raw40441 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40441step0 raw40441; decide +kernel
      have hl : raw40441step0Labels = raw40441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40441 raw40441Labels permutation224 permutation6
    mixedMoment B raw40441step0 raw40441step0Labels = mixedMoment B raw40441step1 raw40441step1Labels := by
      have ha : raw40441step1 = -raw40441step0 := by apply Matrix.ext; change ∀ i j, raw40441step1 i j = -(raw40441step0 i j); unfold raw40441step1 raw40441step0; decide +kernel
      have hl : raw40441step1Labels = raw40441step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3130 node3130Labels := by rfl

def raw40442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40442 raw40442Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw40442 raw40442Labels = mixedMoment B raw40442step0 raw40442step0Labels := by
      have hz : ∀ j, raw40442 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40442step0 = (fun i j => raw40442 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40442step0 raw40442; decide +kernel
      have hl : raw40442step0Labels = raw40442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40442 raw40442Labels permutation434 hz
    mixedMoment B raw40442step0 raw40442step0Labels = mixedMoment B raw40442step1 raw40442step1Labels := by
      have ha : raw40442step1 = (fun i j => raw40442step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40442step1 raw40442step0; decide +kernel
      have hl : raw40442step1Labels = raw40442step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40442step0 raw40442step0Labels permutation50 permutation6
    mixedMoment B raw40442step1 raw40442step1Labels = mixedMoment B raw40442step2 raw40442step2Labels := by
      have ha : raw40442step2 = -raw40442step1 := by apply Matrix.ext; change ∀ i j, raw40442step2 i j = -(raw40442step1 i j); unfold raw40442step2 raw40442step1; decide +kernel
      have hl : raw40442step2Labels = raw40442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw40443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40443step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw40443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40443 raw40443Labels = mixedMoment B node2899 node2899Labels := by
  calc
    mixedMoment B raw40443 raw40443Labels = mixedMoment B raw40443step0 raw40443step0Labels := by
      have hz : ∀ j, raw40443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40443step0 = (fun i j => raw40443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40443step0 raw40443; decide +kernel
      have hl : raw40443step0Labels = raw40443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40443 raw40443Labels permutation434 hz
    mixedMoment B raw40443step0 raw40443step0Labels = mixedMoment B raw40443step1 raw40443step1Labels := by
      have ha : raw40443step1 = (fun i j => raw40443step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40443step1 raw40443step0; decide +kernel
      have hl : raw40443step1Labels = raw40443step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40443step0 raw40443step0Labels permutation137 permutation6
    _ = mixedMoment B node2899 node2899Labels := by rfl

def raw40444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40444 raw40444Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw40444 raw40444Labels = mixedMoment B raw40444step0 raw40444step0Labels := by
      have ha : raw40444step0 = (fun i j => raw40444 (permutation218 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40444step0 raw40444; decide +kernel
      have hl : raw40444step0Labels = raw40444Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40444 raw40444Labels permutation218 permutation6
    mixedMoment B raw40444step0 raw40444step0Labels = mixedMoment B raw40444step1 raw40444step1Labels := by
      have ha : raw40444step1 = -raw40444step0 := by apply Matrix.ext; change ∀ i j, raw40444step1 i j = -(raw40444step0 i j); unfold raw40444step1 raw40444step0; decide +kernel
      have hl : raw40444step1Labels = raw40444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3197 node3197Labels := by rfl

def raw40445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40445 raw40445Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw40445 raw40445Labels = mixedMoment B raw40445step0 raw40445step0Labels := by
      have ha : raw40445step0 = (fun i j => raw40445 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40445step0 raw40445; decide +kernel
      have hl : raw40445step0Labels = raw40445Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40445 raw40445Labels permutation609 permutation6
    _ = mixedMoment B node2895 node2895Labels := by rfl

def raw40446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40446 raw40446Labels = mixedMoment B node3137 node3137Labels := by
  calc
    mixedMoment B raw40446 raw40446Labels = mixedMoment B raw40446step0 raw40446step0Labels := by
      have ha : raw40446step0 = (fun i j => raw40446 (permutation218 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40446step0 raw40446; decide +kernel
      have hl : raw40446step0Labels = raw40446Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40446 raw40446Labels permutation218 permutation6
    mixedMoment B raw40446step0 raw40446step0Labels = mixedMoment B raw40446step1 raw40446step1Labels := by
      have ha : raw40446step1 = -raw40446step0 := by apply Matrix.ext; change ∀ i j, raw40446step1 i j = -(raw40446step0 i j); unfold raw40446step1 raw40446step0; decide +kernel
      have hl : raw40446step1Labels = raw40446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3137 node3137Labels := by rfl

def raw40447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40447 raw40447Labels = mixedMoment B node2890 node2890Labels := by
  calc
    mixedMoment B raw40447 raw40447Labels = mixedMoment B raw40447step0 raw40447step0Labels := by
      have ha : raw40447step0 = (fun i j => raw40447 (permutation611 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40447step0 raw40447; decide +kernel
      have hl : raw40447step0Labels = raw40447Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40447 raw40447Labels permutation611 permutation6
    _ = mixedMoment B node2890 node2890Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
