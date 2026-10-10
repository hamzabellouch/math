import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10240step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10240step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10240step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10240step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10240 raw10240Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw10240 raw10240Labels = mixedMoment B raw10240step0 raw10240step0Labels := by
      have hz : ∀ j, raw10240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10240step0 = (fun i j => raw10240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10240step0 raw10240; decide +kernel
      have hl : raw10240step0Labels = raw10240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10240 raw10240Labels permutation346 hz
    mixedMoment B raw10240step0 raw10240step0Labels = mixedMoment B raw10240step1 raw10240step1Labels := by
      have hz : ∀ j, raw10240step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10240step1 = (fun i j => raw10240step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10240step1 raw10240step0; decide +kernel
      have hl : raw10240step1Labels = raw10240step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10240step0 raw10240step0Labels permutation56 hz
    mixedMoment B raw10240step1 raw10240step1Labels = mixedMoment B raw10240step2 raw10240step2Labels := by
      have ha : raw10240step2 = (fun i j => raw10240step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10240step2 raw10240step1; decide +kernel
      have hl : raw10240step2Labels = raw10240step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10240step1 raw10240step1Labels permutation29 permutation7
    mixedMoment B raw10240step2 raw10240step2Labels = mixedMoment B raw10240step3 raw10240step3Labels := by
      have ha : raw10240step3 = raw10240step2 := by apply Matrix.ext; unfold raw10240step3 raw10240step2; decide +kernel
      have hl : raw10240step2Labels = labelEmbedding10 ∘ raw10240step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10240step2 raw10240step2Labels raw10240step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw10241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10241step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 2, -3]]
def raw10241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10241step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10241step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10241step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10241step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10241 raw10241Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw10241 raw10241Labels = mixedMoment B raw10241step0 raw10241step0Labels := by
      have hz : ∀ j, raw10241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10241step0 = (fun i j => raw10241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10241step0 raw10241; decide +kernel
      have hl : raw10241step0Labels = raw10241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10241 raw10241Labels permutation434 hz
    mixedMoment B raw10241step0 raw10241step0Labels = mixedMoment B raw10241step1 raw10241step1Labels := by
      have hz : ∀ j, raw10241step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10241step1 = (fun i j => raw10241step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10241step1 raw10241step0; decide +kernel
      have hl : raw10241step1Labels = raw10241step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10241step0 raw10241step0Labels permutation80 hz
    mixedMoment B raw10241step1 raw10241step1Labels = mixedMoment B raw10241step2 raw10241step2Labels := by
      have hz : ∀ j, raw10241step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10241step2 = (fun i j => raw10241step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10241step2 raw10241step1; decide +kernel
      have hl : raw10241step2Labels = raw10241step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10241step1 raw10241step1Labels permutation14 hz
    mixedMoment B raw10241step2 raw10241step2Labels = mixedMoment B raw10241step3 raw10241step3Labels := by
      have ha : raw10241step3 = (fun i j => raw10241step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10241step3 raw10241step2; decide +kernel
      have hl : raw10241step3Labels = raw10241step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10241step2 raw10241step2Labels permutation7 permutation6
    mixedMoment B raw10241step3 raw10241step3Labels = mixedMoment B raw10241step4 raw10241step4Labels := by
      have ha : raw10241step4 = raw10241step3 := by apply Matrix.ext; unfold raw10241step4 raw10241step3; decide +kernel
      have hl : raw10241step3Labels = labelEmbedding9 ∘ raw10241step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10241step3 raw10241step3Labels raw10241step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw10242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10242 raw10242Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10242 raw10242Labels = mixedMoment B raw10242step0 raw10242step0Labels := by
      have hz : ∀ j, raw10242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10242step0 = (fun i j => raw10242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10242step0 raw10242; decide +kernel
      have hl : raw10242step0Labels = raw10242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10242 raw10242Labels permutation434 hz
    mixedMoment B raw10242step0 raw10242step0Labels = mixedMoment B raw10242step1 raw10242step1Labels := by
      have hz : ∀ j, raw10242step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10242step1 = (fun i j => raw10242step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10242step1 raw10242step0; decide +kernel
      have hl : raw10242step1Labels = raw10242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10242step0 raw10242step0Labels permutation80 hz
    mixedMoment B raw10242step1 raw10242step1Labels = mixedMoment B raw10242step2 raw10242step2Labels := by
      have ha : raw10242step2 = (fun i j => raw10242step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10242step2 raw10242step1; decide +kernel
      have hl : raw10242step2Labels = raw10242step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10242step1 raw10242step1Labels permutation10 permutation2
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw10243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10243 raw10243Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10243 raw10243Labels = mixedMoment B raw10243step0 raw10243step0Labels := by
      have hz : ∀ j, raw10243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10243step0 = (fun i j => raw10243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10243step0 raw10243; decide +kernel
      have hl : raw10243step0Labels = raw10243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10243 raw10243Labels permutation434 hz
    mixedMoment B raw10243step0 raw10243step0Labels = mixedMoment B raw10243step1 raw10243step1Labels := by
      have ha : raw10243step1 = (fun i j => raw10243step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10243step1 raw10243step0; decide +kernel
      have hl : raw10243step1Labels = raw10243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10243step0 raw10243step0Labels permutation40 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw10244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10244 raw10244Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10244 raw10244Labels = mixedMoment B raw10244step0 raw10244step0Labels := by
      have hz : ∀ j, raw10244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10244step0 = (fun i j => raw10244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10244step0 raw10244; decide +kernel
      have hl : raw10244step0Labels = raw10244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10244 raw10244Labels permutation346 hz
    mixedMoment B raw10244step0 raw10244step0Labels = mixedMoment B raw10244step1 raw10244step1Labels := by
      have ha : raw10244step1 = (fun i j => raw10244step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10244step1 raw10244step0; decide +kernel
      have hl : raw10244step1Labels = raw10244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10244step0 raw10244step0Labels permutation40 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw10245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10245step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10245step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10245 raw10245Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw10245 raw10245Labels = mixedMoment B raw10245step0 raw10245step0Labels := by
      have hz : ∀ j, raw10245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10245step0 = (fun i j => raw10245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10245step0 raw10245; decide +kernel
      have hl : raw10245step0Labels = raw10245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10245 raw10245Labels permutation434 hz
    mixedMoment B raw10245step0 raw10245step0Labels = mixedMoment B raw10245step1 raw10245step1Labels := by
      have hz : ∀ j, raw10245step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10245step1 = (fun i j => raw10245step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10245step1 raw10245step0; decide +kernel
      have hl : raw10245step1Labels = raw10245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10245step0 raw10245step0Labels permutation80 hz
    mixedMoment B raw10245step1 raw10245step1Labels = mixedMoment B raw10245step2 raw10245step2Labels := by
      have ha : raw10245step2 = (fun i j => raw10245step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10245step2 raw10245step1; decide +kernel
      have hl : raw10245step2Labels = raw10245step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10245step1 raw10245step1Labels permutation29 permutation6
    mixedMoment B raw10245step2 raw10245step2Labels = mixedMoment B raw10245step3 raw10245step3Labels := by
      have ha : raw10245step3 = raw10245step2 := by apply Matrix.ext; unfold raw10245step3 raw10245step2; decide +kernel
      have hl : raw10245step2Labels = labelEmbedding9 ∘ raw10245step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10245step2 raw10245step2Labels raw10245step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw10246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10246 raw10246Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10246 raw10246Labels = mixedMoment B raw10246step0 raw10246step0Labels := by
      have hz : ∀ j, raw10246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10246step0 = (fun i j => raw10246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10246step0 raw10246; decide +kernel
      have hl : raw10246step0Labels = raw10246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10246 raw10246Labels permutation434 hz
    mixedMoment B raw10246step0 raw10246step0Labels = mixedMoment B raw10246step1 raw10246step1Labels := by
      have hz : ∀ j, raw10246step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10246step1 = (fun i j => raw10246step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10246step1 raw10246step0; decide +kernel
      have hl : raw10246step1Labels = raw10246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10246step0 raw10246step0Labels permutation56 hz
    mixedMoment B raw10246step1 raw10246step1Labels = mixedMoment B raw10246step2 raw10246step2Labels := by
      have ha : raw10246step2 = (fun i j => raw10246step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10246step2 raw10246step1; decide +kernel
      have hl : raw10246step2Labels = raw10246step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10246step1 raw10246step1Labels permutation10 permutation2
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw10247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10247 raw10247Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10247 raw10247Labels = mixedMoment B raw10247step0 raw10247step0Labels := by
      have hz : ∀ j, raw10247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10247step0 = (fun i j => raw10247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10247step0 raw10247; decide +kernel
      have hl : raw10247step0Labels = raw10247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10247 raw10247Labels permutation434 hz
    mixedMoment B raw10247step0 raw10247step0Labels = mixedMoment B raw10247step1 raw10247step1Labels := by
      have ha : raw10247step1 = (fun i j => raw10247step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10247step1 raw10247step0; decide +kernel
      have hl : raw10247step1Labels = raw10247step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10247step0 raw10247step0Labels permutation34 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw10248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10248 raw10248Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10248 raw10248Labels = mixedMoment B raw10248step0 raw10248step0Labels := by
      have hz : ∀ j, raw10248 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10248step0 = (fun i j => raw10248 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10248step0 raw10248; decide +kernel
      have hl : raw10248step0Labels = raw10248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10248 raw10248Labels permutation265 hz
    mixedMoment B raw10248step0 raw10248step0Labels = mixedMoment B raw10248step1 raw10248step1Labels := by
      have ha : raw10248step1 = (fun i j => raw10248step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10248step1 raw10248step0; decide +kernel
      have hl : raw10248step1Labels = raw10248step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10248step0 raw10248step0Labels permutation40 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw10249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10249step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10249step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10249step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10249step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10249 raw10249Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw10249 raw10249Labels = mixedMoment B raw10249step0 raw10249step0Labels := by
      have hz : ∀ j, raw10249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10249step0 = (fun i j => raw10249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10249step0 raw10249; decide +kernel
      have hl : raw10249step0Labels = raw10249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10249 raw10249Labels permutation434 hz
    mixedMoment B raw10249step0 raw10249step0Labels = mixedMoment B raw10249step1 raw10249step1Labels := by
      have hz : ∀ j, raw10249step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10249step1 = (fun i j => raw10249step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10249step1 raw10249step0; decide +kernel
      have hl : raw10249step1Labels = raw10249step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10249step0 raw10249step0Labels permutation56 hz
    mixedMoment B raw10249step1 raw10249step1Labels = mixedMoment B raw10249step2 raw10249step2Labels := by
      have ha : raw10249step2 = (fun i j => raw10249step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10249step2 raw10249step1; decide +kernel
      have hl : raw10249step2Labels = raw10249step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10249step1 raw10249step1Labels permutation29 permutation6
    mixedMoment B raw10249step2 raw10249step2Labels = mixedMoment B raw10249step3 raw10249step3Labels := by
      have ha : raw10249step3 = raw10249step2 := by apply Matrix.ext; unfold raw10249step3 raw10249step2; decide +kernel
      have hl : raw10249step2Labels = labelEmbedding9 ∘ raw10249step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10249step2 raw10249step2Labels raw10249step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw10250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10250 raw10250Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10250 raw10250Labels = mixedMoment B raw10250step0 raw10250step0Labels := by
      have hz : ∀ j, raw10250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10250step0 = (fun i j => raw10250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10250step0 raw10250; decide +kernel
      have hl : raw10250step0Labels = raw10250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10250 raw10250Labels permutation346 hz
    mixedMoment B raw10250step0 raw10250step0Labels = mixedMoment B raw10250step1 raw10250step1Labels := by
      have hz : ∀ j, raw10250step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10250step1 = (fun i j => raw10250step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10250step1 raw10250step0; decide +kernel
      have hl : raw10250step1Labels = raw10250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10250step0 raw10250step0Labels permutation56 hz
    mixedMoment B raw10250step1 raw10250step1Labels = mixedMoment B raw10250step2 raw10250step2Labels := by
      have ha : raw10250step2 = (fun i j => raw10250step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10250step2 raw10250step1; decide +kernel
      have hl : raw10250step2Labels = raw10250step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10250step1 raw10250step1Labels permutation10 permutation2
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw10251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10251 raw10251Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10251 raw10251Labels = mixedMoment B raw10251step0 raw10251step0Labels := by
      have hz : ∀ j, raw10251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10251step0 = (fun i j => raw10251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10251step0 raw10251; decide +kernel
      have hl : raw10251step0Labels = raw10251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10251 raw10251Labels permutation346 hz
    mixedMoment B raw10251step0 raw10251step0Labels = mixedMoment B raw10251step1 raw10251step1Labels := by
      have ha : raw10251step1 = (fun i j => raw10251step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10251step1 raw10251step0; decide +kernel
      have hl : raw10251step1Labels = raw10251step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10251step0 raw10251step0Labels permutation34 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw10252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10252 raw10252Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10252 raw10252Labels = mixedMoment B raw10252step0 raw10252step0Labels := by
      have hz : ∀ j, raw10252 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10252step0 = (fun i j => raw10252 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10252step0 raw10252; decide +kernel
      have hl : raw10252step0Labels = raw10252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10252 raw10252Labels permutation265 hz
    mixedMoment B raw10252step0 raw10252step0Labels = mixedMoment B raw10252step1 raw10252step1Labels := by
      have ha : raw10252step1 = (fun i j => raw10252step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10252step1 raw10252step0; decide +kernel
      have hl : raw10252step1Labels = raw10252step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10252step0 raw10252step0Labels permutation34 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw10253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10253step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10253step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10253step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10253step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10253 raw10253Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw10253 raw10253Labels = mixedMoment B raw10253step0 raw10253step0Labels := by
      have hz : ∀ j, raw10253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10253step0 = (fun i j => raw10253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10253step0 raw10253; decide +kernel
      have hl : raw10253step0Labels = raw10253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10253 raw10253Labels permutation346 hz
    mixedMoment B raw10253step0 raw10253step0Labels = mixedMoment B raw10253step1 raw10253step1Labels := by
      have hz : ∀ j, raw10253step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10253step1 = (fun i j => raw10253step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10253step1 raw10253step0; decide +kernel
      have hl : raw10253step1Labels = raw10253step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10253step0 raw10253step0Labels permutation56 hz
    mixedMoment B raw10253step1 raw10253step1Labels = mixedMoment B raw10253step2 raw10253step2Labels := by
      have ha : raw10253step2 = (fun i j => raw10253step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10253step2 raw10253step1; decide +kernel
      have hl : raw10253step2Labels = raw10253step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10253step1 raw10253step1Labels permutation29 permutation6
    mixedMoment B raw10253step2 raw10253step2Labels = mixedMoment B raw10253step3 raw10253step3Labels := by
      have ha : raw10253step3 = raw10253step2 := by apply Matrix.ext; unfold raw10253step3 raw10253step2; decide +kernel
      have hl : raw10253step2Labels = labelEmbedding9 ∘ raw10253step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10253step2 raw10253step2Labels raw10253step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw10254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10254step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw10254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10254 raw10254Labels = mixedMoment B node4626 node4626Labels := by
  calc
    mixedMoment B raw10254 raw10254Labels = mixedMoment B raw10254step0 raw10254step0Labels := by
      have hz : ∀ j, raw10254 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10254step0 = (fun i j => raw10254 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10254step0 raw10254; decide +kernel
      have hl : raw10254step0Labels = raw10254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10254 raw10254Labels permutation434 hz
    mixedMoment B raw10254step0 raw10254step0Labels = mixedMoment B raw10254step1 raw10254step1Labels := by
      have hz : ∀ j, raw10254step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10254step1 = (fun i j => raw10254step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10254step1 raw10254step0; decide +kernel
      have hl : raw10254step1Labels = raw10254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10254step0 raw10254step0Labels permutation80 hz
    mixedMoment B raw10254step1 raw10254step1Labels = mixedMoment B raw10254step2 raw10254step2Labels := by
      have hz : ∀ j, raw10254step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10254step2 = (fun i j => raw10254step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10254step2 raw10254step1; decide +kernel
      have hl : raw10254step2Labels = raw10254step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10254step1 raw10254step1Labels permutation14 hz
    _ = mixedMoment B node4626 node4626Labels := by rfl

def raw10255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10255 raw10255Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw10255 raw10255Labels = mixedMoment B raw10255step0 raw10255step0Labels := by
      have hz : ∀ j, raw10255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10255step0 = (fun i j => raw10255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10255step0 raw10255; decide +kernel
      have hl : raw10255step0Labels = raw10255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10255 raw10255Labels permutation434 hz
    mixedMoment B raw10255step0 raw10255step0Labels = mixedMoment B raw10255step1 raw10255step1Labels := by
      have hz : ∀ j, raw10255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10255step1 = (fun i j => raw10255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10255step1 raw10255step0; decide +kernel
      have hl : raw10255step1Labels = raw10255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10255step0 raw10255step0Labels permutation80 hz
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw10256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10256 raw10256Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw10256 raw10256Labels = mixedMoment B raw10256step0 raw10256step0Labels := by
      have hz : ∀ j, raw10256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10256step0 = (fun i j => raw10256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10256step0 raw10256; decide +kernel
      have hl : raw10256step0Labels = raw10256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10256 raw10256Labels permutation434 hz
    mixedMoment B raw10256step0 raw10256step0Labels = mixedMoment B raw10256step1 raw10256step1Labels := by
      have hz : ∀ j, raw10256step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10256step1 = (fun i j => raw10256step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10256step1 raw10256step0; decide +kernel
      have hl : raw10256step1Labels = raw10256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10256step0 raw10256step0Labels permutation56 hz
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw10257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10257step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10257 raw10257Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw10257 raw10257Labels = mixedMoment B raw10257step0 raw10257step0Labels := by
      have hz : ∀ j, raw10257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10257step0 = (fun i j => raw10257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10257step0 raw10257; decide +kernel
      have hl : raw10257step0Labels = raw10257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10257 raw10257Labels permutation346 hz
    mixedMoment B raw10257step0 raw10257step0Labels = mixedMoment B raw10257step1 raw10257step1Labels := by
      have hz : ∀ j, raw10257step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10257step1 = (fun i j => raw10257step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10257step1 raw10257step0; decide +kernel
      have hl : raw10257step1Labels = raw10257step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10257step0 raw10257step0Labels permutation56 hz
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw10258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10258step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -3, 1], ![1, 2, -3]]
def raw10258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10258step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw10258step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10258 raw10258Labels = mixedMoment B node5311 node5311Labels := by
  calc
    mixedMoment B raw10258 raw10258Labels = mixedMoment B raw10258step0 raw10258step0Labels := by
      have hz : ∀ j, raw10258 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10258step0 = (fun i j => raw10258 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10258step0 raw10258; decide +kernel
      have hl : raw10258step0Labels = raw10258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10258 raw10258Labels permutation434 hz
    mixedMoment B raw10258step0 raw10258step0Labels = mixedMoment B raw10258step1 raw10258step1Labels := by
      have hz : ∀ j, raw10258step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10258step1 = (fun i j => raw10258step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10258step1 raw10258step0; decide +kernel
      have hl : raw10258step1Labels = raw10258step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10258step0 raw10258step0Labels permutation80 hz
    mixedMoment B raw10258step1 raw10258step1Labels = mixedMoment B raw10258step2 raw10258step2Labels := by
      have hz : ∀ j, raw10258step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10258step2 = (fun i j => raw10258step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10258step2 raw10258step1; decide +kernel
      have hl : raw10258step2Labels = raw10258step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10258step1 raw10258step1Labels permutation14 hz
    mixedMoment B raw10258step2 raw10258step2Labels = mixedMoment B raw10258step3 raw10258step3Labels := by
      have ha : raw10258step3 = (fun i j => raw10258step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10258step3 raw10258step2; decide +kernel
      have hl : raw10258step3Labels = raw10258step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10258step2 raw10258step2Labels permutation3 permutation2
    _ = mixedMoment B node5311 node5311Labels := by rfl

def raw10259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10259step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw10259step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw10259step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10259 raw10259Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw10259 raw10259Labels = mixedMoment B raw10259step0 raw10259step0Labels := by
      have hz : ∀ j, raw10259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10259step0 = (fun i j => raw10259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10259step0 raw10259; decide +kernel
      have hl : raw10259step0Labels = raw10259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259 raw10259Labels permutation434 hz
    mixedMoment B raw10259step0 raw10259step0Labels = mixedMoment B raw10259step1 raw10259step1Labels := by
      have hz : ∀ j, raw10259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10259step1 = (fun i j => raw10259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10259step1 raw10259step0; decide +kernel
      have hl : raw10259step1Labels = raw10259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259step0 raw10259step0Labels permutation80 hz
    mixedMoment B raw10259step1 raw10259step1Labels = mixedMoment B raw10259step2 raw10259step2Labels := by
      have hz : ∀ j, raw10259step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10259step2 = (fun i j => raw10259step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10259step2 raw10259step1; decide +kernel
      have hl : raw10259step2Labels = raw10259step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259step1 raw10259step1Labels permutation14 hz
    mixedMoment B raw10259step2 raw10259step2Labels = mixedMoment B raw10259step3 raw10259step3Labels := by
      have ha : raw10259step3 = (fun i j => raw10259step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10259step3 raw10259step2; decide +kernel
      have hl : raw10259step3Labels = raw10259step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10259step2 raw10259step2Labels permutation7 permutation2
    mixedMoment B raw10259step3 raw10259step3Labels = mixedMoment B raw10259step4 raw10259step4Labels := by
      have ha : raw10259step4 = -raw10259step3 := by apply Matrix.ext; change ∀ i j, raw10259step4 i j = -(raw10259step3 i j); unfold raw10259step4 raw10259step3; decide +kernel
      have hl : raw10259step4Labels = raw10259step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw10260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10260step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10260 raw10260Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw10260 raw10260Labels = mixedMoment B raw10260step0 raw10260step0Labels := by
      have hz : ∀ j, raw10260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10260step0 = (fun i j => raw10260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10260step0 raw10260; decide +kernel
      have hl : raw10260step0Labels = raw10260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10260 raw10260Labels permutation434 hz
    mixedMoment B raw10260step0 raw10260step0Labels = mixedMoment B raw10260step1 raw10260step1Labels := by
      have hz : ∀ j, raw10260step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10260step1 = (fun i j => raw10260step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10260step1 raw10260step0; decide +kernel
      have hl : raw10260step1Labels = raw10260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10260step0 raw10260step0Labels permutation80 hz
    mixedMoment B raw10260step1 raw10260step1Labels = mixedMoment B raw10260step2 raw10260step2Labels := by
      have ha : raw10260step2 = (fun i j => raw10260step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10260step2 raw10260step1; decide +kernel
      have hl : raw10260step2Labels = raw10260step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10260step1 raw10260step1Labels permutation29 permutation6
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw10261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10261step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10261 raw10261Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw10261 raw10261Labels = mixedMoment B raw10261step0 raw10261step0Labels := by
      have hz : ∀ j, raw10261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10261step0 = (fun i j => raw10261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10261step0 raw10261; decide +kernel
      have hl : raw10261step0Labels = raw10261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10261 raw10261Labels permutation434 hz
    mixedMoment B raw10261step0 raw10261step0Labels = mixedMoment B raw10261step1 raw10261step1Labels := by
      have hz : ∀ j, raw10261step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10261step1 = (fun i j => raw10261step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10261step1 raw10261step0; decide +kernel
      have hl : raw10261step1Labels = raw10261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10261step0 raw10261step0Labels permutation56 hz
    mixedMoment B raw10261step1 raw10261step1Labels = mixedMoment B raw10261step2 raw10261step2Labels := by
      have ha : raw10261step2 = (fun i j => raw10261step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10261step2 raw10261step1; decide +kernel
      have hl : raw10261step2Labels = raw10261step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10261step1 raw10261step1Labels permutation29 permutation6
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw10262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10262step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10262step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10262 raw10262Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw10262 raw10262Labels = mixedMoment B raw10262step0 raw10262step0Labels := by
      have hz : ∀ j, raw10262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10262step0 = (fun i j => raw10262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10262step0 raw10262; decide +kernel
      have hl : raw10262step0Labels = raw10262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10262 raw10262Labels permutation346 hz
    mixedMoment B raw10262step0 raw10262step0Labels = mixedMoment B raw10262step1 raw10262step1Labels := by
      have hz : ∀ j, raw10262step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10262step1 = (fun i j => raw10262step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10262step1 raw10262step0; decide +kernel
      have hl : raw10262step1Labels = raw10262step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10262step0 raw10262step0Labels permutation56 hz
    mixedMoment B raw10262step1 raw10262step1Labels = mixedMoment B raw10262step2 raw10262step2Labels := by
      have ha : raw10262step2 = (fun i j => raw10262step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10262step2 raw10262step1; decide +kernel
      have hl : raw10262step2Labels = raw10262step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10262step1 raw10262step1Labels permutation29 permutation6
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw10263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10263step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10263step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw10263step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10263step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw10263step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10263 raw10263Labels = mixedMoment B node3124 node3124Labels := by
  calc
    mixedMoment B raw10263 raw10263Labels = mixedMoment B raw10263step0 raw10263step0Labels := by
      have hz : ∀ j, raw10263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10263step0 = (fun i j => raw10263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10263step0 raw10263; decide +kernel
      have hl : raw10263step0Labels = raw10263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10263 raw10263Labels permutation434 hz
    mixedMoment B raw10263step0 raw10263step0Labels = mixedMoment B raw10263step1 raw10263step1Labels := by
      have hz : ∀ j, raw10263step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10263step1 = (fun i j => raw10263step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10263step1 raw10263step0; decide +kernel
      have hl : raw10263step1Labels = raw10263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10263step0 raw10263step0Labels permutation80 hz
    mixedMoment B raw10263step1 raw10263step1Labels = mixedMoment B raw10263step2 raw10263step2Labels := by
      have hz : ∀ j, raw10263step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10263step2 = (fun i j => raw10263step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10263step2 raw10263step1; decide +kernel
      have hl : raw10263step2Labels = raw10263step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10263step1 raw10263step1Labels permutation14 hz
    mixedMoment B raw10263step2 raw10263step2Labels = mixedMoment B raw10263step3 raw10263step3Labels := by
      have ha : raw10263step3 = (fun i j => raw10263step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10263step3 raw10263step2; decide +kernel
      have hl : raw10263step3Labels = raw10263step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10263step2 raw10263step2Labels permutation7 permutation6
    _ = mixedMoment B node3124 node3124Labels := by rfl

def raw10264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10264step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10264step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 2, -3]]
def raw10264step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10264step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10264step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10264 raw10264Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw10264 raw10264Labels = mixedMoment B raw10264step0 raw10264step0Labels := by
      have hz : ∀ j, raw10264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10264step0 = (fun i j => raw10264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10264step0 raw10264; decide +kernel
      have hl : raw10264step0Labels = raw10264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10264 raw10264Labels permutation434 hz
    mixedMoment B raw10264step0 raw10264step0Labels = mixedMoment B raw10264step1 raw10264step1Labels := by
      have hz : ∀ j, raw10264step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10264step1 = (fun i j => raw10264step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10264step1 raw10264step0; decide +kernel
      have hl : raw10264step1Labels = raw10264step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10264step0 raw10264step0Labels permutation80 hz
    mixedMoment B raw10264step1 raw10264step1Labels = mixedMoment B raw10264step2 raw10264step2Labels := by
      have hz : ∀ j, raw10264step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10264step2 = (fun i j => raw10264step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10264step2 raw10264step1; decide +kernel
      have hl : raw10264step2Labels = raw10264step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10264step1 raw10264step1Labels permutation14 hz
    mixedMoment B raw10264step2 raw10264step2Labels = mixedMoment B raw10264step3 raw10264step3Labels := by
      have ha : raw10264step3 = (fun i j => raw10264step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10264step3 raw10264step2; decide +kernel
      have hl : raw10264step3Labels = raw10264step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10264step2 raw10264step2Labels permutation7 permutation6
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw10265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10265step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10265step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10265 raw10265Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw10265 raw10265Labels = mixedMoment B raw10265step0 raw10265step0Labels := by
      have hz : ∀ j, raw10265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10265step0 = (fun i j => raw10265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10265step0 raw10265; decide +kernel
      have hl : raw10265step0Labels = raw10265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10265 raw10265Labels permutation434 hz
    mixedMoment B raw10265step0 raw10265step0Labels = mixedMoment B raw10265step1 raw10265step1Labels := by
      have hz : ∀ j, raw10265step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10265step1 = (fun i j => raw10265step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10265step1 raw10265step0; decide +kernel
      have hl : raw10265step1Labels = raw10265step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10265step0 raw10265step0Labels permutation80 hz
    mixedMoment B raw10265step1 raw10265step1Labels = mixedMoment B raw10265step2 raw10265step2Labels := by
      have ha : raw10265step2 = (fun i j => raw10265step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10265step2 raw10265step1; decide +kernel
      have hl : raw10265step2Labels = raw10265step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10265step1 raw10265step1Labels permutation8 permutation3
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw10266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10266step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10266 raw10266Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw10266 raw10266Labels = mixedMoment B raw10266step0 raw10266step0Labels := by
      have hz : ∀ j, raw10266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10266step0 = (fun i j => raw10266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10266step0 raw10266; decide +kernel
      have hl : raw10266step0Labels = raw10266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10266 raw10266Labels permutation434 hz
    mixedMoment B raw10266step0 raw10266step0Labels = mixedMoment B raw10266step1 raw10266step1Labels := by
      have ha : raw10266step1 = (fun i j => raw10266step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10266step1 raw10266step0; decide +kernel
      have hl : raw10266step1Labels = raw10266step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10266step0 raw10266step0Labels permutation38 permutation3
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw10267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10267 raw10267Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw10267 raw10267Labels = mixedMoment B raw10267step0 raw10267step0Labels := by
      have hz : ∀ j, raw10267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10267step0 = (fun i j => raw10267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10267step0 raw10267; decide +kernel
      have hl : raw10267step0Labels = raw10267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10267 raw10267Labels permutation346 hz
    mixedMoment B raw10267step0 raw10267step0Labels = mixedMoment B raw10267step1 raw10267step1Labels := by
      have ha : raw10267step1 = (fun i j => raw10267step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10267step1 raw10267step0; decide +kernel
      have hl : raw10267step1Labels = raw10267step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10267step0 raw10267step0Labels permutation38 permutation3
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw10268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10268step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10268 raw10268Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw10268 raw10268Labels = mixedMoment B raw10268step0 raw10268step0Labels := by
      have hz : ∀ j, raw10268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10268step0 = (fun i j => raw10268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10268step0 raw10268; decide +kernel
      have hl : raw10268step0Labels = raw10268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10268 raw10268Labels permutation434 hz
    mixedMoment B raw10268step0 raw10268step0Labels = mixedMoment B raw10268step1 raw10268step1Labels := by
      have hz : ∀ j, raw10268step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10268step1 = (fun i j => raw10268step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10268step1 raw10268step0; decide +kernel
      have hl : raw10268step1Labels = raw10268step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10268step0 raw10268step0Labels permutation80 hz
    mixedMoment B raw10268step1 raw10268step1Labels = mixedMoment B raw10268step2 raw10268step2Labels := by
      have ha : raw10268step2 = (fun i j => raw10268step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10268step2 raw10268step1; decide +kernel
      have hl : raw10268step2Labels = raw10268step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10268step1 raw10268step1Labels permutation10 permutation3
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw10269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10269step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10269step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10269step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10269 raw10269Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw10269 raw10269Labels = mixedMoment B raw10269step0 raw10269step0Labels := by
      have hz : ∀ j, raw10269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10269step0 = (fun i j => raw10269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10269step0 raw10269; decide +kernel
      have hl : raw10269step0Labels = raw10269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10269 raw10269Labels permutation434 hz
    mixedMoment B raw10269step0 raw10269step0Labels = mixedMoment B raw10269step1 raw10269step1Labels := by
      have hz : ∀ j, raw10269step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10269step1 = (fun i j => raw10269step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10269step1 raw10269step0; decide +kernel
      have hl : raw10269step1Labels = raw10269step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10269step0 raw10269step0Labels permutation80 hz
    mixedMoment B raw10269step1 raw10269step1Labels = mixedMoment B raw10269step2 raw10269step2Labels := by
      have ha : raw10269step2 = (fun i j => raw10269step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10269step2 raw10269step1; decide +kernel
      have hl : raw10269step2Labels = raw10269step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10269step1 raw10269step1Labels permutation29 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw10270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10270step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10270 raw10270Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw10270 raw10270Labels = mixedMoment B raw10270step0 raw10270step0Labels := by
      have hz : ∀ j, raw10270 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10270step0 = (fun i j => raw10270 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10270step0 raw10270; decide +kernel
      have hl : raw10270step0Labels = raw10270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10270 raw10270Labels permutation434 hz
    mixedMoment B raw10270step0 raw10270step0Labels = mixedMoment B raw10270step1 raw10270step1Labels := by
      have hz : ∀ j, raw10270step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10270step1 = (fun i j => raw10270step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10270step1 raw10270step0; decide +kernel
      have hl : raw10270step1Labels = raw10270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10270step0 raw10270step0Labels permutation56 hz
    mixedMoment B raw10270step1 raw10270step1Labels = mixedMoment B raw10270step2 raw10270step2Labels := by
      have ha : raw10270step2 = (fun i j => raw10270step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10270step2 raw10270step1; decide +kernel
      have hl : raw10270step2Labels = raw10270step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10270step1 raw10270step1Labels permutation8 permutation3
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw10271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10271 raw10271Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw10271 raw10271Labels = mixedMoment B raw10271step0 raw10271step0Labels := by
      have hz : ∀ j, raw10271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10271step0 = (fun i j => raw10271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10271step0 raw10271; decide +kernel
      have hl : raw10271step0Labels = raw10271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10271 raw10271Labels permutation434 hz
    mixedMoment B raw10271step0 raw10271step0Labels = mixedMoment B raw10271step1 raw10271step1Labels := by
      have ha : raw10271step1 = (fun i j => raw10271step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10271step1 raw10271step0; decide +kernel
      have hl : raw10271step1Labels = raw10271step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10271step0 raw10271step0Labels permutation32 permutation3
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw10272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10272 raw10272Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw10272 raw10272Labels = mixedMoment B raw10272step0 raw10272step0Labels := by
      have hz : ∀ j, raw10272 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10272step0 = (fun i j => raw10272 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10272step0 raw10272; decide +kernel
      have hl : raw10272step0Labels = raw10272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10272 raw10272Labels permutation265 hz
    mixedMoment B raw10272step0 raw10272step0Labels = mixedMoment B raw10272step1 raw10272step1Labels := by
      have ha : raw10272step1 = (fun i j => raw10272step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10272step1 raw10272step0; decide +kernel
      have hl : raw10272step1Labels = raw10272step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10272step0 raw10272step0Labels permutation38 permutation3
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw10273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10273step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10273 raw10273Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw10273 raw10273Labels = mixedMoment B raw10273step0 raw10273step0Labels := by
      have hz : ∀ j, raw10273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10273step0 = (fun i j => raw10273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10273step0 raw10273; decide +kernel
      have hl : raw10273step0Labels = raw10273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10273 raw10273Labels permutation434 hz
    mixedMoment B raw10273step0 raw10273step0Labels = mixedMoment B raw10273step1 raw10273step1Labels := by
      have hz : ∀ j, raw10273step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10273step1 = (fun i j => raw10273step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10273step1 raw10273step0; decide +kernel
      have hl : raw10273step1Labels = raw10273step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10273step0 raw10273step0Labels permutation56 hz
    mixedMoment B raw10273step1 raw10273step1Labels = mixedMoment B raw10273step2 raw10273step2Labels := by
      have ha : raw10273step2 = (fun i j => raw10273step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10273step2 raw10273step1; decide +kernel
      have hl : raw10273step2Labels = raw10273step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10273step1 raw10273step1Labels permutation10 permutation3
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw10274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10274step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10274 raw10274Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw10274 raw10274Labels = mixedMoment B raw10274step0 raw10274step0Labels := by
      have hz : ∀ j, raw10274 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10274step0 = (fun i j => raw10274 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10274step0 raw10274; decide +kernel
      have hl : raw10274step0Labels = raw10274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10274 raw10274Labels permutation434 hz
    mixedMoment B raw10274step0 raw10274step0Labels = mixedMoment B raw10274step1 raw10274step1Labels := by
      have hz : ∀ j, raw10274step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10274step1 = (fun i j => raw10274step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10274step1 raw10274step0; decide +kernel
      have hl : raw10274step1Labels = raw10274step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10274step0 raw10274step0Labels permutation56 hz
    mixedMoment B raw10274step1 raw10274step1Labels = mixedMoment B raw10274step2 raw10274step2Labels := by
      have ha : raw10274step2 = (fun i j => raw10274step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10274step2 raw10274step1; decide +kernel
      have hl : raw10274step2Labels = raw10274step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10274step1 raw10274step1Labels permutation29 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw10275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10275step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10275 raw10275Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw10275 raw10275Labels = mixedMoment B raw10275step0 raw10275step0Labels := by
      have hz : ∀ j, raw10275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10275step0 = (fun i j => raw10275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10275step0 raw10275; decide +kernel
      have hl : raw10275step0Labels = raw10275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10275 raw10275Labels permutation346 hz
    mixedMoment B raw10275step0 raw10275step0Labels = mixedMoment B raw10275step1 raw10275step1Labels := by
      have hz : ∀ j, raw10275step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10275step1 = (fun i j => raw10275step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10275step1 raw10275step0; decide +kernel
      have hl : raw10275step1Labels = raw10275step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10275step0 raw10275step0Labels permutation56 hz
    mixedMoment B raw10275step1 raw10275step1Labels = mixedMoment B raw10275step2 raw10275step2Labels := by
      have ha : raw10275step2 = (fun i j => raw10275step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10275step2 raw10275step1; decide +kernel
      have hl : raw10275step2Labels = raw10275step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10275step1 raw10275step1Labels permutation8 permutation3
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw10276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10276 raw10276Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw10276 raw10276Labels = mixedMoment B raw10276step0 raw10276step0Labels := by
      have hz : ∀ j, raw10276 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10276step0 = (fun i j => raw10276 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10276step0 raw10276; decide +kernel
      have hl : raw10276step0Labels = raw10276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10276 raw10276Labels permutation346 hz
    mixedMoment B raw10276step0 raw10276step0Labels = mixedMoment B raw10276step1 raw10276step1Labels := by
      have ha : raw10276step1 = (fun i j => raw10276step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10276step1 raw10276step0; decide +kernel
      have hl : raw10276step1Labels = raw10276step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10276step0 raw10276step0Labels permutation32 permutation3
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw10277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10277 raw10277Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw10277 raw10277Labels = mixedMoment B raw10277step0 raw10277step0Labels := by
      have hz : ∀ j, raw10277 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10277step0 = (fun i j => raw10277 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10277step0 raw10277; decide +kernel
      have hl : raw10277step0Labels = raw10277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10277 raw10277Labels permutation265 hz
    mixedMoment B raw10277step0 raw10277step0Labels = mixedMoment B raw10277step1 raw10277step1Labels := by
      have ha : raw10277step1 = (fun i j => raw10277step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10277step1 raw10277step0; decide +kernel
      have hl : raw10277step1Labels = raw10277step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10277step0 raw10277step0Labels permutation32 permutation3
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw10278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10278step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10278step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10278 raw10278Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw10278 raw10278Labels = mixedMoment B raw10278step0 raw10278step0Labels := by
      have hz : ∀ j, raw10278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10278step0 = (fun i j => raw10278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10278step0 raw10278; decide +kernel
      have hl : raw10278step0Labels = raw10278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10278 raw10278Labels permutation346 hz
    mixedMoment B raw10278step0 raw10278step0Labels = mixedMoment B raw10278step1 raw10278step1Labels := by
      have hz : ∀ j, raw10278step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10278step1 = (fun i j => raw10278step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10278step1 raw10278step0; decide +kernel
      have hl : raw10278step1Labels = raw10278step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10278step0 raw10278step0Labels permutation56 hz
    mixedMoment B raw10278step1 raw10278step1Labels = mixedMoment B raw10278step2 raw10278step2Labels := by
      have ha : raw10278step2 = (fun i j => raw10278step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10278step2 raw10278step1; decide +kernel
      have hl : raw10278step2Labels = raw10278step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10278step1 raw10278step1Labels permutation10 permutation3
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw10279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10279step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10279step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10279step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10279step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10279 raw10279Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw10279 raw10279Labels = mixedMoment B raw10279step0 raw10279step0Labels := by
      have hz : ∀ j, raw10279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10279step0 = (fun i j => raw10279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10279step0 raw10279; decide +kernel
      have hl : raw10279step0Labels = raw10279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10279 raw10279Labels permutation346 hz
    mixedMoment B raw10279step0 raw10279step0Labels = mixedMoment B raw10279step1 raw10279step1Labels := by
      have hz : ∀ j, raw10279step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10279step1 = (fun i j => raw10279step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10279step1 raw10279step0; decide +kernel
      have hl : raw10279step1Labels = raw10279step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10279step0 raw10279step0Labels permutation56 hz
    mixedMoment B raw10279step1 raw10279step1Labels = mixedMoment B raw10279step2 raw10279step2Labels := by
      have ha : raw10279step2 = (fun i j => raw10279step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10279step2 raw10279step1; decide +kernel
      have hl : raw10279step2Labels = raw10279step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10279step1 raw10279step1Labels permutation29 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw10280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10280step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10280step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw10280step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10280step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw10280step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10280 raw10280Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw10280 raw10280Labels = mixedMoment B raw10280step0 raw10280step0Labels := by
      have hz : ∀ j, raw10280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10280step0 = (fun i j => raw10280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10280step0 raw10280; decide +kernel
      have hl : raw10280step0Labels = raw10280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10280 raw10280Labels permutation434 hz
    mixedMoment B raw10280step0 raw10280step0Labels = mixedMoment B raw10280step1 raw10280step1Labels := by
      have hz : ∀ j, raw10280step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10280step1 = (fun i j => raw10280step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10280step1 raw10280step0; decide +kernel
      have hl : raw10280step1Labels = raw10280step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10280step0 raw10280step0Labels permutation80 hz
    mixedMoment B raw10280step1 raw10280step1Labels = mixedMoment B raw10280step2 raw10280step2Labels := by
      have hz : ∀ j, raw10280step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10280step2 = (fun i j => raw10280step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10280step2 raw10280step1; decide +kernel
      have hl : raw10280step2Labels = raw10280step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10280step1 raw10280step1Labels permutation14 hz
    mixedMoment B raw10280step2 raw10280step2Labels = mixedMoment B raw10280step3 raw10280step3Labels := by
      have ha : raw10280step3 = (fun i j => raw10280step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10280step3 raw10280step2; decide +kernel
      have hl : raw10280step3Labels = raw10280step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10280step2 raw10280step2Labels permutation3 permutation3
    _ = mixedMoment B node1310 node1310Labels := by rfl

def raw10281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10281step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10281step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw10281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10281 raw10281Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw10281 raw10281Labels = mixedMoment B raw10281step0 raw10281step0Labels := by
      have hz : ∀ j, raw10281 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10281step0 = (fun i j => raw10281 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10281step0 raw10281; decide +kernel
      have hl : raw10281step0Labels = raw10281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10281 raw10281Labels permutation434 hz
    mixedMoment B raw10281step0 raw10281step0Labels = mixedMoment B raw10281step1 raw10281step1Labels := by
      have hz : ∀ j, raw10281step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10281step1 = (fun i j => raw10281step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10281step1 raw10281step0; decide +kernel
      have hl : raw10281step1Labels = raw10281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10281step0 raw10281step0Labels permutation80 hz
    mixedMoment B raw10281step1 raw10281step1Labels = mixedMoment B raw10281step2 raw10281step2Labels := by
      have ha : raw10281step2 = (fun i j => raw10281step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10281step2 raw10281step1; decide +kernel
      have hl : raw10281step2Labels = raw10281step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10281step1 raw10281step1Labels permutation9 permutation3
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw10282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10282step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw10282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10282 raw10282Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw10282 raw10282Labels = mixedMoment B raw10282step0 raw10282step0Labels := by
      have hz : ∀ j, raw10282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10282step0 = (fun i j => raw10282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10282step0 raw10282; decide +kernel
      have hl : raw10282step0Labels = raw10282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10282 raw10282Labels permutation434 hz
    mixedMoment B raw10282step0 raw10282step0Labels = mixedMoment B raw10282step1 raw10282step1Labels := by
      have hz : ∀ j, raw10282step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10282step1 = (fun i j => raw10282step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10282step1 raw10282step0; decide +kernel
      have hl : raw10282step1Labels = raw10282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10282step0 raw10282step0Labels permutation56 hz
    mixedMoment B raw10282step1 raw10282step1Labels = mixedMoment B raw10282step2 raw10282step2Labels := by
      have ha : raw10282step2 = (fun i j => raw10282step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10282step2 raw10282step1; decide +kernel
      have hl : raw10282step2Labels = raw10282step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10282step1 raw10282step1Labels permutation9 permutation3
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw10283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10283step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw10283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10283 raw10283Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw10283 raw10283Labels = mixedMoment B raw10283step0 raw10283step0Labels := by
      have hz : ∀ j, raw10283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10283step0 = (fun i j => raw10283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10283step0 raw10283; decide +kernel
      have hl : raw10283step0Labels = raw10283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10283 raw10283Labels permutation346 hz
    mixedMoment B raw10283step0 raw10283step0Labels = mixedMoment B raw10283step1 raw10283step1Labels := by
      have hz : ∀ j, raw10283step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10283step1 = (fun i j => raw10283step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10283step1 raw10283step0; decide +kernel
      have hl : raw10283step1Labels = raw10283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10283step0 raw10283step0Labels permutation56 hz
    mixedMoment B raw10283step1 raw10283step1Labels = mixedMoment B raw10283step2 raw10283step2Labels := by
      have ha : raw10283step2 = (fun i j => raw10283step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10283step2 raw10283step1; decide +kernel
      have hl : raw10283step2Labels = raw10283step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10283step1 raw10283step1Labels permutation9 permutation3
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw10284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10284step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10284step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -3, 1], ![1, 2, -3]]
def raw10284step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10284step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw10284step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10284 raw10284Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw10284 raw10284Labels = mixedMoment B raw10284step0 raw10284step0Labels := by
      have hz : ∀ j, raw10284 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10284step0 = (fun i j => raw10284 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10284step0 raw10284; decide +kernel
      have hl : raw10284step0Labels = raw10284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10284 raw10284Labels permutation434 hz
    mixedMoment B raw10284step0 raw10284step0Labels = mixedMoment B raw10284step1 raw10284step1Labels := by
      have hz : ∀ j, raw10284step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10284step1 = (fun i j => raw10284step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10284step1 raw10284step0; decide +kernel
      have hl : raw10284step1Labels = raw10284step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10284step0 raw10284step0Labels permutation80 hz
    mixedMoment B raw10284step1 raw10284step1Labels = mixedMoment B raw10284step2 raw10284step2Labels := by
      have hz : ∀ j, raw10284step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10284step2 = (fun i j => raw10284step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10284step2 raw10284step1; decide +kernel
      have hl : raw10284step2Labels = raw10284step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10284step1 raw10284step1Labels permutation14 hz
    mixedMoment B raw10284step2 raw10284step2Labels = mixedMoment B raw10284step3 raw10284step3Labels := by
      have ha : raw10284step3 = (fun i j => raw10284step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10284step3 raw10284step2; decide +kernel
      have hl : raw10284step3Labels = raw10284step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10284step2 raw10284step2Labels permutation7 permutation6
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw10285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10285step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10285step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw10285step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10285step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw10285step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10285 raw10285Labels = mixedMoment B node1308 node1308Labels := by
  calc
    mixedMoment B raw10285 raw10285Labels = mixedMoment B raw10285step0 raw10285step0Labels := by
      have hz : ∀ j, raw10285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10285step0 = (fun i j => raw10285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10285step0 raw10285; decide +kernel
      have hl : raw10285step0Labels = raw10285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10285 raw10285Labels permutation434 hz
    mixedMoment B raw10285step0 raw10285step0Labels = mixedMoment B raw10285step1 raw10285step1Labels := by
      have hz : ∀ j, raw10285step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10285step1 = (fun i j => raw10285step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10285step1 raw10285step0; decide +kernel
      have hl : raw10285step1Labels = raw10285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10285step0 raw10285step0Labels permutation80 hz
    mixedMoment B raw10285step1 raw10285step1Labels = mixedMoment B raw10285step2 raw10285step2Labels := by
      have hz : ∀ j, raw10285step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10285step2 = (fun i j => raw10285step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10285step2 raw10285step1; decide +kernel
      have hl : raw10285step2Labels = raw10285step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10285step1 raw10285step1Labels permutation14 hz
    mixedMoment B raw10285step2 raw10285step2Labels = mixedMoment B raw10285step3 raw10285step3Labels := by
      have ha : raw10285step3 = (fun i j => raw10285step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10285step3 raw10285step2; decide +kernel
      have hl : raw10285step3Labels = raw10285step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10285step2 raw10285step2Labels permutation2 permutation3
    _ = mixedMoment B node1308 node1308Labels := by rfl

def raw10286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10286step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10286step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10286step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw10286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10286 raw10286Labels = mixedMoment B node2966 node2966Labels := by
  calc
    mixedMoment B raw10286 raw10286Labels = mixedMoment B raw10286step0 raw10286step0Labels := by
      have hz : ∀ j, raw10286 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10286step0 = (fun i j => raw10286 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10286step0 raw10286; decide +kernel
      have hl : raw10286step0Labels = raw10286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10286 raw10286Labels permutation434 hz
    mixedMoment B raw10286step0 raw10286step0Labels = mixedMoment B raw10286step1 raw10286step1Labels := by
      have hz : ∀ j, raw10286step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10286step1 = (fun i j => raw10286step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10286step1 raw10286step0; decide +kernel
      have hl : raw10286step1Labels = raw10286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10286step0 raw10286step0Labels permutation80 hz
    mixedMoment B raw10286step1 raw10286step1Labels = mixedMoment B raw10286step2 raw10286step2Labels := by
      have ha : raw10286step2 = (fun i j => raw10286step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10286step2 raw10286step1; decide +kernel
      have hl : raw10286step2Labels = raw10286step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10286step1 raw10286step1Labels permutation8 permutation3
    _ = mixedMoment B node2966 node2966Labels := by rfl

def raw10287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10287step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10287step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw10287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10287 raw10287Labels = mixedMoment B node2966 node2966Labels := by
  calc
    mixedMoment B raw10287 raw10287Labels = mixedMoment B raw10287step0 raw10287step0Labels := by
      have hz : ∀ j, raw10287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10287step0 = (fun i j => raw10287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10287step0 raw10287; decide +kernel
      have hl : raw10287step0Labels = raw10287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10287 raw10287Labels permutation434 hz
    mixedMoment B raw10287step0 raw10287step0Labels = mixedMoment B raw10287step1 raw10287step1Labels := by
      have hz : ∀ j, raw10287step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10287step1 = (fun i j => raw10287step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10287step1 raw10287step0; decide +kernel
      have hl : raw10287step1Labels = raw10287step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10287step0 raw10287step0Labels permutation56 hz
    mixedMoment B raw10287step1 raw10287step1Labels = mixedMoment B raw10287step2 raw10287step2Labels := by
      have ha : raw10287step2 = (fun i j => raw10287step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10287step2 raw10287step1; decide +kernel
      have hl : raw10287step2Labels = raw10287step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10287step1 raw10287step1Labels permutation8 permutation3
    _ = mixedMoment B node2966 node2966Labels := by rfl

def raw10288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10288step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw10288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10288 raw10288Labels = mixedMoment B node2966 node2966Labels := by
  calc
    mixedMoment B raw10288 raw10288Labels = mixedMoment B raw10288step0 raw10288step0Labels := by
      have hz : ∀ j, raw10288 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10288step0 = (fun i j => raw10288 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10288step0 raw10288; decide +kernel
      have hl : raw10288step0Labels = raw10288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10288 raw10288Labels permutation346 hz
    mixedMoment B raw10288step0 raw10288step0Labels = mixedMoment B raw10288step1 raw10288step1Labels := by
      have hz : ∀ j, raw10288step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10288step1 = (fun i j => raw10288step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10288step1 raw10288step0; decide +kernel
      have hl : raw10288step1Labels = raw10288step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10288step0 raw10288step0Labels permutation56 hz
    mixedMoment B raw10288step1 raw10288step1Labels = mixedMoment B raw10288step2 raw10288step2Labels := by
      have ha : raw10288step2 = (fun i j => raw10288step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10288step2 raw10288step1; decide +kernel
      have hl : raw10288step2Labels = raw10288step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10288step1 raw10288step1Labels permutation8 permutation3
    _ = mixedMoment B node2966 node2966Labels := by rfl

def raw10289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10289step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10289step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10289step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10289step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw10289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10289 raw10289Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw10289 raw10289Labels = mixedMoment B raw10289step0 raw10289step0Labels := by
      have hz : ∀ j, raw10289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10289step0 = (fun i j => raw10289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10289step0 raw10289; decide +kernel
      have hl : raw10289step0Labels = raw10289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10289 raw10289Labels permutation434 hz
    mixedMoment B raw10289step0 raw10289step0Labels = mixedMoment B raw10289step1 raw10289step1Labels := by
      have hz : ∀ j, raw10289step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10289step1 = (fun i j => raw10289step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10289step1 raw10289step0; decide +kernel
      have hl : raw10289step1Labels = raw10289step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10289step0 raw10289step0Labels permutation80 hz
    mixedMoment B raw10289step1 raw10289step1Labels = mixedMoment B raw10289step2 raw10289step2Labels := by
      have hz : ∀ j, raw10289step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10289step2 = (fun i j => raw10289step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10289step2 raw10289step1; decide +kernel
      have hl : raw10289step2Labels = raw10289step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10289step1 raw10289step1Labels permutation14 hz
    mixedMoment B raw10289step2 raw10289step2Labels = mixedMoment B raw10289step3 raw10289step3Labels := by
      have ha : raw10289step3 = (fun i j => raw10289step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10289step3 raw10289step2; decide +kernel
      have hl : raw10289step3Labels = raw10289step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10289step2 raw10289step2Labels permutation2 permutation3
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw10290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10290step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10290step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10290step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10290 raw10290Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw10290 raw10290Labels = mixedMoment B raw10290step0 raw10290step0Labels := by
      have hz : ∀ j, raw10290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10290step0 = (fun i j => raw10290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10290step0 raw10290; decide +kernel
      have hl : raw10290step0Labels = raw10290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10290 raw10290Labels permutation434 hz
    mixedMoment B raw10290step0 raw10290step0Labels = mixedMoment B raw10290step1 raw10290step1Labels := by
      have hz : ∀ j, raw10290step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10290step1 = (fun i j => raw10290step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10290step1 raw10290step0; decide +kernel
      have hl : raw10290step1Labels = raw10290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10290step0 raw10290step0Labels permutation80 hz
    mixedMoment B raw10290step1 raw10290step1Labels = mixedMoment B raw10290step2 raw10290step2Labels := by
      have ha : raw10290step2 = (fun i j => raw10290step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10290step2 raw10290step1; decide +kernel
      have hl : raw10290step2Labels = raw10290step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10290step1 raw10290step1Labels permutation29 permutation7
    mixedMoment B raw10290step2 raw10290step2Labels = mixedMoment B raw10290step3 raw10290step3Labels := by
      have ha : raw10290step3 = raw10290step2 := by apply Matrix.ext; unfold raw10290step3 raw10290step2; decide +kernel
      have hl : raw10290step2Labels = labelEmbedding1 ∘ raw10290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10290step2 raw10290step2Labels raw10290step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw10291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10291step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10291step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10291step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10291step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10291 raw10291Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw10291 raw10291Labels = mixedMoment B raw10291step0 raw10291step0Labels := by
      have hz : ∀ j, raw10291 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10291step0 = (fun i j => raw10291 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10291step0 raw10291; decide +kernel
      have hl : raw10291step0Labels = raw10291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10291 raw10291Labels permutation434 hz
    mixedMoment B raw10291step0 raw10291step0Labels = mixedMoment B raw10291step1 raw10291step1Labels := by
      have hz : ∀ j, raw10291step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10291step1 = (fun i j => raw10291step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10291step1 raw10291step0; decide +kernel
      have hl : raw10291step1Labels = raw10291step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10291step0 raw10291step0Labels permutation56 hz
    mixedMoment B raw10291step1 raw10291step1Labels = mixedMoment B raw10291step2 raw10291step2Labels := by
      have ha : raw10291step2 = (fun i j => raw10291step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10291step2 raw10291step1; decide +kernel
      have hl : raw10291step2Labels = raw10291step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10291step1 raw10291step1Labels permutation29 permutation7
    mixedMoment B raw10291step2 raw10291step2Labels = mixedMoment B raw10291step3 raw10291step3Labels := by
      have ha : raw10291step3 = raw10291step2 := by apply Matrix.ext; unfold raw10291step3 raw10291step2; decide +kernel
      have hl : raw10291step2Labels = labelEmbedding1 ∘ raw10291step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10291step2 raw10291step2Labels raw10291step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw10292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10292step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10292step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10292step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10292step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10292step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10292step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10292 raw10292Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw10292 raw10292Labels = mixedMoment B raw10292step0 raw10292step0Labels := by
      have hz : ∀ j, raw10292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10292step0 = (fun i j => raw10292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10292step0 raw10292; decide +kernel
      have hl : raw10292step0Labels = raw10292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10292 raw10292Labels permutation346 hz
    mixedMoment B raw10292step0 raw10292step0Labels = mixedMoment B raw10292step1 raw10292step1Labels := by
      have hz : ∀ j, raw10292step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10292step1 = (fun i j => raw10292step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10292step1 raw10292step0; decide +kernel
      have hl : raw10292step1Labels = raw10292step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10292step0 raw10292step0Labels permutation56 hz
    mixedMoment B raw10292step1 raw10292step1Labels = mixedMoment B raw10292step2 raw10292step2Labels := by
      have ha : raw10292step2 = (fun i j => raw10292step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10292step2 raw10292step1; decide +kernel
      have hl : raw10292step2Labels = raw10292step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10292step1 raw10292step1Labels permutation29 permutation7
    mixedMoment B raw10292step2 raw10292step2Labels = mixedMoment B raw10292step3 raw10292step3Labels := by
      have ha : raw10292step3 = raw10292step2 := by apply Matrix.ext; unfold raw10292step3 raw10292step2; decide +kernel
      have hl : raw10292step2Labels = labelEmbedding1 ∘ raw10292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10292step2 raw10292step2Labels raw10292step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw10293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10293step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10293step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 2, -3]]
def raw10293step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10293step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw10293step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10293step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw10293step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10293 raw10293Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw10293 raw10293Labels = mixedMoment B raw10293step0 raw10293step0Labels := by
      have hz : ∀ j, raw10293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10293step0 = (fun i j => raw10293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10293step0 raw10293; decide +kernel
      have hl : raw10293step0Labels = raw10293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10293 raw10293Labels permutation434 hz
    mixedMoment B raw10293step0 raw10293step0Labels = mixedMoment B raw10293step1 raw10293step1Labels := by
      have hz : ∀ j, raw10293step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10293step1 = (fun i j => raw10293step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10293step1 raw10293step0; decide +kernel
      have hl : raw10293step1Labels = raw10293step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10293step0 raw10293step0Labels permutation80 hz
    mixedMoment B raw10293step1 raw10293step1Labels = mixedMoment B raw10293step2 raw10293step2Labels := by
      have hz : ∀ j, raw10293step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10293step2 = (fun i j => raw10293step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10293step2 raw10293step1; decide +kernel
      have hl : raw10293step2Labels = raw10293step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10293step1 raw10293step1Labels permutation14 hz
    mixedMoment B raw10293step2 raw10293step2Labels = mixedMoment B raw10293step3 raw10293step3Labels := by
      have ha : raw10293step3 = (fun i j => raw10293step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10293step3 raw10293step2; decide +kernel
      have hl : raw10293step3Labels = raw10293step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10293step2 raw10293step2Labels permutation7 permutation7
    mixedMoment B raw10293step3 raw10293step3Labels = mixedMoment B raw10293step4 raw10293step4Labels := by
      have ha : raw10293step4 = raw10293step3 := by apply Matrix.ext; unfold raw10293step4 raw10293step3; decide +kernel
      have hl : raw10293step3Labels = labelEmbedding1 ∘ raw10293step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10293step3 raw10293step3Labels raw10293step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw10294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10294step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10294step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10294step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10294step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10294step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10294 raw10294Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10294 raw10294Labels = mixedMoment B raw10294step0 raw10294step0Labels := by
      have hz : ∀ j, raw10294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10294step0 = (fun i j => raw10294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10294step0 raw10294; decide +kernel
      have hl : raw10294step0Labels = raw10294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10294 raw10294Labels permutation434 hz
    mixedMoment B raw10294step0 raw10294step0Labels = mixedMoment B raw10294step1 raw10294step1Labels := by
      have hz : ∀ j, raw10294step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10294step1 = (fun i j => raw10294step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10294step1 raw10294step0; decide +kernel
      have hl : raw10294step1Labels = raw10294step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10294step0 raw10294step0Labels permutation80 hz
    mixedMoment B raw10294step1 raw10294step1Labels = mixedMoment B raw10294step2 raw10294step2Labels := by
      have ha : raw10294step2 = (fun i j => raw10294step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10294step2 raw10294step1; decide +kernel
      have hl : raw10294step2Labels = raw10294step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10294step1 raw10294step1Labels permutation29 permutation7
    mixedMoment B raw10294step2 raw10294step2Labels = mixedMoment B raw10294step3 raw10294step3Labels := by
      have ha : raw10294step3 = raw10294step2 := by apply Matrix.ext; unfold raw10294step3 raw10294step2; decide +kernel
      have hl : raw10294step2Labels = labelEmbedding1 ∘ raw10294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10294step2 raw10294step2Labels raw10294step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw10295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10295step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10295 raw10295Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10295 raw10295Labels = mixedMoment B raw10295step0 raw10295step0Labels := by
      have hz : ∀ j, raw10295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10295step0 = (fun i j => raw10295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10295step0 raw10295; decide +kernel
      have hl : raw10295step0Labels = raw10295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10295 raw10295Labels permutation434 hz
    mixedMoment B raw10295step0 raw10295step0Labels = mixedMoment B raw10295step1 raw10295step1Labels := by
      have ha : raw10295step1 = (fun i j => raw10295step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10295step1 raw10295step0; decide +kernel
      have hl : raw10295step1Labels = raw10295step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10295step0 raw10295step0Labels permutation137 permutation7
    mixedMoment B raw10295step1 raw10295step1Labels = mixedMoment B raw10295step2 raw10295step2Labels := by
      have ha : raw10295step2 = raw10295step1 := by apply Matrix.ext; unfold raw10295step2 raw10295step1; decide +kernel
      have hl : raw10295step1Labels = labelEmbedding1 ∘ raw10295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10295step1 raw10295step1Labels raw10295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw10296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10296step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10296step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10296 raw10296Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10296 raw10296Labels = mixedMoment B raw10296step0 raw10296step0Labels := by
      have hz : ∀ j, raw10296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10296step0 = (fun i j => raw10296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10296step0 raw10296; decide +kernel
      have hl : raw10296step0Labels = raw10296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10296 raw10296Labels permutation346 hz
    mixedMoment B raw10296step0 raw10296step0Labels = mixedMoment B raw10296step1 raw10296step1Labels := by
      have ha : raw10296step1 = (fun i j => raw10296step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10296step1 raw10296step0; decide +kernel
      have hl : raw10296step1Labels = raw10296step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10296step0 raw10296step0Labels permutation137 permutation7
    mixedMoment B raw10296step1 raw10296step1Labels = mixedMoment B raw10296step2 raw10296step2Labels := by
      have ha : raw10296step2 = raw10296step1 := by apply Matrix.ext; unfold raw10296step2 raw10296step1; decide +kernel
      have hl : raw10296step1Labels = labelEmbedding1 ∘ raw10296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10296step1 raw10296step1Labels raw10296step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw10297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10297step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10297step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10297step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10297 raw10297Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw10297 raw10297Labels = mixedMoment B raw10297step0 raw10297step0Labels := by
      have hz : ∀ j, raw10297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10297step0 = (fun i j => raw10297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10297step0 raw10297; decide +kernel
      have hl : raw10297step0Labels = raw10297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10297 raw10297Labels permutation434 hz
    mixedMoment B raw10297step0 raw10297step0Labels = mixedMoment B raw10297step1 raw10297step1Labels := by
      have hz : ∀ j, raw10297step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10297step1 = (fun i j => raw10297step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10297step1 raw10297step0; decide +kernel
      have hl : raw10297step1Labels = raw10297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10297step0 raw10297step0Labels permutation80 hz
    mixedMoment B raw10297step1 raw10297step1Labels = mixedMoment B raw10297step2 raw10297step2Labels := by
      have ha : raw10297step2 = (fun i j => raw10297step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10297step2 raw10297step1; decide +kernel
      have hl : raw10297step2Labels = raw10297step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10297step1 raw10297step1Labels permutation29 permutation7
    mixedMoment B raw10297step2 raw10297step2Labels = mixedMoment B raw10297step3 raw10297step3Labels := by
      have ha : raw10297step3 = raw10297step2 := by apply Matrix.ext; unfold raw10297step3 raw10297step2; decide +kernel
      have hl : raw10297step2Labels = labelEmbedding1 ∘ raw10297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10297step2 raw10297step2Labels raw10297step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw10298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10298step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10298step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10298step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10298step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10298 raw10298Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10298 raw10298Labels = mixedMoment B raw10298step0 raw10298step0Labels := by
      have hz : ∀ j, raw10298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10298step0 = (fun i j => raw10298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10298step0 raw10298; decide +kernel
      have hl : raw10298step0Labels = raw10298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10298 raw10298Labels permutation434 hz
    mixedMoment B raw10298step0 raw10298step0Labels = mixedMoment B raw10298step1 raw10298step1Labels := by
      have hz : ∀ j, raw10298step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10298step1 = (fun i j => raw10298step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10298step1 raw10298step0; decide +kernel
      have hl : raw10298step1Labels = raw10298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10298step0 raw10298step0Labels permutation56 hz
    mixedMoment B raw10298step1 raw10298step1Labels = mixedMoment B raw10298step2 raw10298step2Labels := by
      have ha : raw10298step2 = (fun i j => raw10298step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10298step2 raw10298step1; decide +kernel
      have hl : raw10298step2Labels = raw10298step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10298step1 raw10298step1Labels permutation29 permutation7
    mixedMoment B raw10298step2 raw10298step2Labels = mixedMoment B raw10298step3 raw10298step3Labels := by
      have ha : raw10298step3 = raw10298step2 := by apply Matrix.ext; unfold raw10298step3 raw10298step2; decide +kernel
      have hl : raw10298step2Labels = labelEmbedding1 ∘ raw10298step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10298step2 raw10298step2Labels raw10298step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw10299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10299step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10299 raw10299Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10299 raw10299Labels = mixedMoment B raw10299step0 raw10299step0Labels := by
      have hz : ∀ j, raw10299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10299step0 = (fun i j => raw10299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10299step0 raw10299; decide +kernel
      have hl : raw10299step0Labels = raw10299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10299 raw10299Labels permutation434 hz
    mixedMoment B raw10299step0 raw10299step0Labels = mixedMoment B raw10299step1 raw10299step1Labels := by
      have ha : raw10299step1 = (fun i j => raw10299step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10299step1 raw10299step0; decide +kernel
      have hl : raw10299step1Labels = raw10299step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10299step0 raw10299step0Labels permutation143 permutation7
    mixedMoment B raw10299step1 raw10299step1Labels = mixedMoment B raw10299step2 raw10299step2Labels := by
      have ha : raw10299step2 = raw10299step1 := by apply Matrix.ext; unfold raw10299step2 raw10299step1; decide +kernel
      have hl : raw10299step1Labels = labelEmbedding1 ∘ raw10299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10299step1 raw10299step1Labels raw10299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw10300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10300step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10300 raw10300Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10300 raw10300Labels = mixedMoment B raw10300step0 raw10300step0Labels := by
      have hz : ∀ j, raw10300 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10300step0 = (fun i j => raw10300 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10300step0 raw10300; decide +kernel
      have hl : raw10300step0Labels = raw10300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10300 raw10300Labels permutation265 hz
    mixedMoment B raw10300step0 raw10300step0Labels = mixedMoment B raw10300step1 raw10300step1Labels := by
      have ha : raw10300step1 = (fun i j => raw10300step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10300step1 raw10300step0; decide +kernel
      have hl : raw10300step1Labels = raw10300step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10300step0 raw10300step0Labels permutation137 permutation7
    mixedMoment B raw10300step1 raw10300step1Labels = mixedMoment B raw10300step2 raw10300step2Labels := by
      have ha : raw10300step2 = raw10300step1 := by apply Matrix.ext; unfold raw10300step2 raw10300step1; decide +kernel
      have hl : raw10300step1Labels = labelEmbedding1 ∘ raw10300step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10300step1 raw10300step1Labels raw10300step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw10301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10301step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10301step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10301step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10301step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10301 raw10301Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw10301 raw10301Labels = mixedMoment B raw10301step0 raw10301step0Labels := by
      have hz : ∀ j, raw10301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10301step0 = (fun i j => raw10301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10301step0 raw10301; decide +kernel
      have hl : raw10301step0Labels = raw10301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10301 raw10301Labels permutation434 hz
    mixedMoment B raw10301step0 raw10301step0Labels = mixedMoment B raw10301step1 raw10301step1Labels := by
      have hz : ∀ j, raw10301step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10301step1 = (fun i j => raw10301step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10301step1 raw10301step0; decide +kernel
      have hl : raw10301step1Labels = raw10301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10301step0 raw10301step0Labels permutation56 hz
    mixedMoment B raw10301step1 raw10301step1Labels = mixedMoment B raw10301step2 raw10301step2Labels := by
      have ha : raw10301step2 = (fun i j => raw10301step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10301step2 raw10301step1; decide +kernel
      have hl : raw10301step2Labels = raw10301step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10301step1 raw10301step1Labels permutation29 permutation7
    mixedMoment B raw10301step2 raw10301step2Labels = mixedMoment B raw10301step3 raw10301step3Labels := by
      have ha : raw10301step3 = raw10301step2 := by apply Matrix.ext; unfold raw10301step3 raw10301step2; decide +kernel
      have hl : raw10301step2Labels = labelEmbedding1 ∘ raw10301step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10301step2 raw10301step2Labels raw10301step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw10302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10302step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10302 raw10302Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10302 raw10302Labels = mixedMoment B raw10302step0 raw10302step0Labels := by
      have hz : ∀ j, raw10302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10302step0 = (fun i j => raw10302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10302step0 raw10302; decide +kernel
      have hl : raw10302step0Labels = raw10302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10302 raw10302Labels permutation346 hz
    mixedMoment B raw10302step0 raw10302step0Labels = mixedMoment B raw10302step1 raw10302step1Labels := by
      have hz : ∀ j, raw10302step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10302step1 = (fun i j => raw10302step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10302step1 raw10302step0; decide +kernel
      have hl : raw10302step1Labels = raw10302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10302step0 raw10302step0Labels permutation56 hz
    mixedMoment B raw10302step1 raw10302step1Labels = mixedMoment B raw10302step2 raw10302step2Labels := by
      have ha : raw10302step2 = (fun i j => raw10302step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10302step2 raw10302step1; decide +kernel
      have hl : raw10302step2Labels = raw10302step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10302step1 raw10302step1Labels permutation29 permutation7
    mixedMoment B raw10302step2 raw10302step2Labels = mixedMoment B raw10302step3 raw10302step3Labels := by
      have ha : raw10302step3 = raw10302step2 := by apply Matrix.ext; unfold raw10302step3 raw10302step2; decide +kernel
      have hl : raw10302step2Labels = labelEmbedding1 ∘ raw10302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10302step2 raw10302step2Labels raw10302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw10303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10303 raw10303Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10303 raw10303Labels = mixedMoment B raw10303step0 raw10303step0Labels := by
      have hz : ∀ j, raw10303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10303step0 = (fun i j => raw10303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10303step0 raw10303; decide +kernel
      have hl : raw10303step0Labels = raw10303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10303 raw10303Labels permutation346 hz
    mixedMoment B raw10303step0 raw10303step0Labels = mixedMoment B raw10303step1 raw10303step1Labels := by
      have ha : raw10303step1 = (fun i j => raw10303step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10303step1 raw10303step0; decide +kernel
      have hl : raw10303step1Labels = raw10303step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10303step0 raw10303step0Labels permutation143 permutation7
    mixedMoment B raw10303step1 raw10303step1Labels = mixedMoment B raw10303step2 raw10303step2Labels := by
      have ha : raw10303step2 = raw10303step1 := by apply Matrix.ext; unfold raw10303step2 raw10303step1; decide +kernel
      have hl : raw10303step1Labels = labelEmbedding1 ∘ raw10303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10303step1 raw10303step1Labels raw10303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw10304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10304step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10304 raw10304Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10304 raw10304Labels = mixedMoment B raw10304step0 raw10304step0Labels := by
      have hz : ∀ j, raw10304 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10304step0 = (fun i j => raw10304 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10304step0 raw10304; decide +kernel
      have hl : raw10304step0Labels = raw10304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10304 raw10304Labels permutation265 hz
    mixedMoment B raw10304step0 raw10304step0Labels = mixedMoment B raw10304step1 raw10304step1Labels := by
      have ha : raw10304step1 = (fun i j => raw10304step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10304step1 raw10304step0; decide +kernel
      have hl : raw10304step1Labels = raw10304step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10304step0 raw10304step0Labels permutation143 permutation7
    mixedMoment B raw10304step1 raw10304step1Labels = mixedMoment B raw10304step2 raw10304step2Labels := by
      have ha : raw10304step2 = raw10304step1 := by apply Matrix.ext; unfold raw10304step2 raw10304step1; decide +kernel
      have hl : raw10304step1Labels = labelEmbedding1 ∘ raw10304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10304step1 raw10304step1Labels raw10304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw10305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10305step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10305step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10305step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10305step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10305step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10305step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10305 raw10305Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw10305 raw10305Labels = mixedMoment B raw10305step0 raw10305step0Labels := by
      have hz : ∀ j, raw10305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10305step0 = (fun i j => raw10305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10305step0 raw10305; decide +kernel
      have hl : raw10305step0Labels = raw10305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10305 raw10305Labels permutation346 hz
    mixedMoment B raw10305step0 raw10305step0Labels = mixedMoment B raw10305step1 raw10305step1Labels := by
      have hz : ∀ j, raw10305step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10305step1 = (fun i j => raw10305step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10305step1 raw10305step0; decide +kernel
      have hl : raw10305step1Labels = raw10305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10305step0 raw10305step0Labels permutation56 hz
    mixedMoment B raw10305step1 raw10305step1Labels = mixedMoment B raw10305step2 raw10305step2Labels := by
      have ha : raw10305step2 = (fun i j => raw10305step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10305step2 raw10305step1; decide +kernel
      have hl : raw10305step2Labels = raw10305step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10305step1 raw10305step1Labels permutation29 permutation7
    mixedMoment B raw10305step2 raw10305step2Labels = mixedMoment B raw10305step3 raw10305step3Labels := by
      have ha : raw10305step3 = raw10305step2 := by apply Matrix.ext; unfold raw10305step3 raw10305step2; decide +kernel
      have hl : raw10305step2Labels = labelEmbedding1 ∘ raw10305step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10305step2 raw10305step2Labels raw10305step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw10306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10306step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10306step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw10306step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10306step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw10306step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10306step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw10306step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10306 raw10306Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw10306 raw10306Labels = mixedMoment B raw10306step0 raw10306step0Labels := by
      have hz : ∀ j, raw10306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10306step0 = (fun i j => raw10306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10306step0 raw10306; decide +kernel
      have hl : raw10306step0Labels = raw10306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10306 raw10306Labels permutation434 hz
    mixedMoment B raw10306step0 raw10306step0Labels = mixedMoment B raw10306step1 raw10306step1Labels := by
      have hz : ∀ j, raw10306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10306step1 = (fun i j => raw10306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10306step1 raw10306step0; decide +kernel
      have hl : raw10306step1Labels = raw10306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10306step0 raw10306step0Labels permutation80 hz
    mixedMoment B raw10306step1 raw10306step1Labels = mixedMoment B raw10306step2 raw10306step2Labels := by
      have hz : ∀ j, raw10306step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10306step2 = (fun i j => raw10306step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10306step2 raw10306step1; decide +kernel
      have hl : raw10306step2Labels = raw10306step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10306step1 raw10306step1Labels permutation14 hz
    mixedMoment B raw10306step2 raw10306step2Labels = mixedMoment B raw10306step3 raw10306step3Labels := by
      have ha : raw10306step3 = (fun i j => raw10306step2 (permutation5 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10306step3 raw10306step2; decide +kernel
      have hl : raw10306step3Labels = raw10306step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10306step2 raw10306step2Labels permutation5 permutation5
    mixedMoment B raw10306step3 raw10306step3Labels = mixedMoment B raw10306step4 raw10306step4Labels := by
      have ha : raw10306step4 = raw10306step3 := by apply Matrix.ext; unfold raw10306step4 raw10306step3; decide +kernel
      have hl : raw10306step3Labels = labelEmbedding1 ∘ raw10306step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10306step3 raw10306step3Labels raw10306step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2780 node2780Labels := by rfl

def raw10307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10307step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10307step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10307step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10307step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10307 raw10307Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw10307 raw10307Labels = mixedMoment B raw10307step0 raw10307step0Labels := by
      have hz : ∀ j, raw10307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10307step0 = (fun i j => raw10307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10307step0 raw10307; decide +kernel
      have hl : raw10307step0Labels = raw10307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10307 raw10307Labels permutation434 hz
    mixedMoment B raw10307step0 raw10307step0Labels = mixedMoment B raw10307step1 raw10307step1Labels := by
      have hz : ∀ j, raw10307step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10307step1 = (fun i j => raw10307step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10307step1 raw10307step0; decide +kernel
      have hl : raw10307step1Labels = raw10307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10307step0 raw10307step0Labels permutation80 hz
    mixedMoment B raw10307step1 raw10307step1Labels = mixedMoment B raw10307step2 raw10307step2Labels := by
      have ha : raw10307step2 = (fun i j => raw10307step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10307step2 raw10307step1; decide +kernel
      have hl : raw10307step2Labels = raw10307step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10307step1 raw10307step1Labels permutation29 permutation7
    mixedMoment B raw10307step2 raw10307step2Labels = mixedMoment B raw10307step3 raw10307step3Labels := by
      have ha : raw10307step3 = raw10307step2 := by apply Matrix.ext; unfold raw10307step3 raw10307step2; decide +kernel
      have hl : raw10307step2Labels = labelEmbedding1 ∘ raw10307step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10307step2 raw10307step2Labels raw10307step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw10308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10308step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10308step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10308step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10308step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10308step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10308 raw10308Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw10308 raw10308Labels = mixedMoment B raw10308step0 raw10308step0Labels := by
      have hz : ∀ j, raw10308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10308step0 = (fun i j => raw10308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10308step0 raw10308; decide +kernel
      have hl : raw10308step0Labels = raw10308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10308 raw10308Labels permutation434 hz
    mixedMoment B raw10308step0 raw10308step0Labels = mixedMoment B raw10308step1 raw10308step1Labels := by
      have hz : ∀ j, raw10308step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10308step1 = (fun i j => raw10308step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10308step1 raw10308step0; decide +kernel
      have hl : raw10308step1Labels = raw10308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10308step0 raw10308step0Labels permutation56 hz
    mixedMoment B raw10308step1 raw10308step1Labels = mixedMoment B raw10308step2 raw10308step2Labels := by
      have ha : raw10308step2 = (fun i j => raw10308step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10308step2 raw10308step1; decide +kernel
      have hl : raw10308step2Labels = raw10308step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10308step1 raw10308step1Labels permutation29 permutation7
    mixedMoment B raw10308step2 raw10308step2Labels = mixedMoment B raw10308step3 raw10308step3Labels := by
      have ha : raw10308step3 = raw10308step2 := by apply Matrix.ext; unfold raw10308step3 raw10308step2; decide +kernel
      have hl : raw10308step2Labels = labelEmbedding1 ∘ raw10308step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10308step2 raw10308step2Labels raw10308step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw10309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10309step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10309step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10309step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10309step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10309 raw10309Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw10309 raw10309Labels = mixedMoment B raw10309step0 raw10309step0Labels := by
      have hz : ∀ j, raw10309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10309step0 = (fun i j => raw10309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10309step0 raw10309; decide +kernel
      have hl : raw10309step0Labels = raw10309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10309 raw10309Labels permutation346 hz
    mixedMoment B raw10309step0 raw10309step0Labels = mixedMoment B raw10309step1 raw10309step1Labels := by
      have hz : ∀ j, raw10309step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10309step1 = (fun i j => raw10309step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10309step1 raw10309step0; decide +kernel
      have hl : raw10309step1Labels = raw10309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10309step0 raw10309step0Labels permutation56 hz
    mixedMoment B raw10309step1 raw10309step1Labels = mixedMoment B raw10309step2 raw10309step2Labels := by
      have ha : raw10309step2 = (fun i j => raw10309step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10309step2 raw10309step1; decide +kernel
      have hl : raw10309step2Labels = raw10309step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10309step1 raw10309step1Labels permutation29 permutation7
    mixedMoment B raw10309step2 raw10309step2Labels = mixedMoment B raw10309step3 raw10309step3Labels := by
      have ha : raw10309step3 = raw10309step2 := by apply Matrix.ext; unfold raw10309step3 raw10309step2; decide +kernel
      have hl : raw10309step2Labels = labelEmbedding1 ∘ raw10309step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10309step2 raw10309step2Labels raw10309step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw10310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10310step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10310step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -3, 1], ![1, 2, -3]]
def raw10310step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10310step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw10310step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10310step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw10310step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10310 raw10310Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw10310 raw10310Labels = mixedMoment B raw10310step0 raw10310step0Labels := by
      have hz : ∀ j, raw10310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10310step0 = (fun i j => raw10310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10310step0 raw10310; decide +kernel
      have hl : raw10310step0Labels = raw10310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10310 raw10310Labels permutation434 hz
    mixedMoment B raw10310step0 raw10310step0Labels = mixedMoment B raw10310step1 raw10310step1Labels := by
      have hz : ∀ j, raw10310step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10310step1 = (fun i j => raw10310step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10310step1 raw10310step0; decide +kernel
      have hl : raw10310step1Labels = raw10310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10310step0 raw10310step0Labels permutation80 hz
    mixedMoment B raw10310step1 raw10310step1Labels = mixedMoment B raw10310step2 raw10310step2Labels := by
      have hz : ∀ j, raw10310step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10310step2 = (fun i j => raw10310step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10310step2 raw10310step1; decide +kernel
      have hl : raw10310step2Labels = raw10310step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10310step1 raw10310step1Labels permutation14 hz
    mixedMoment B raw10310step2 raw10310step2Labels = mixedMoment B raw10310step3 raw10310step3Labels := by
      have ha : raw10310step3 = (fun i j => raw10310step2 (permutation4 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10310step3 raw10310step2; decide +kernel
      have hl : raw10310step3Labels = raw10310step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10310step2 raw10310step2Labels permutation4 permutation5
    mixedMoment B raw10310step3 raw10310step3Labels = mixedMoment B raw10310step4 raw10310step4Labels := by
      have ha : raw10310step4 = raw10310step3 := by apply Matrix.ext; unfold raw10310step4 raw10310step3; decide +kernel
      have hl : raw10310step3Labels = labelEmbedding1 ∘ raw10310step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10310step3 raw10310step3Labels raw10310step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw10311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10311step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10311step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10311step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10311step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw10311step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10311step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw10311step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10311 raw10311Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw10311 raw10311Labels = mixedMoment B raw10311step0 raw10311step0Labels := by
      have hz : ∀ j, raw10311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10311step0 = (fun i j => raw10311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10311step0 raw10311; decide +kernel
      have hl : raw10311step0Labels = raw10311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311 raw10311Labels permutation434 hz
    mixedMoment B raw10311step0 raw10311step0Labels = mixedMoment B raw10311step1 raw10311step1Labels := by
      have hz : ∀ j, raw10311step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10311step1 = (fun i j => raw10311step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10311step1 raw10311step0; decide +kernel
      have hl : raw10311step1Labels = raw10311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311step0 raw10311step0Labels permutation80 hz
    mixedMoment B raw10311step1 raw10311step1Labels = mixedMoment B raw10311step2 raw10311step2Labels := by
      have hz : ∀ j, raw10311step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10311step2 = (fun i j => raw10311step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10311step2 raw10311step1; decide +kernel
      have hl : raw10311step2Labels = raw10311step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10311step1 raw10311step1Labels permutation14 hz
    mixedMoment B raw10311step2 raw10311step2Labels = mixedMoment B raw10311step3 raw10311step3Labels := by
      have ha : raw10311step3 = (fun i j => raw10311step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10311step3 raw10311step2; decide +kernel
      have hl : raw10311step3Labels = raw10311step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10311step2 raw10311step2Labels permutation7 permutation7
    mixedMoment B raw10311step3 raw10311step3Labels = mixedMoment B raw10311step4 raw10311step4Labels := by
      have ha : raw10311step4 = raw10311step3 := by apply Matrix.ext; unfold raw10311step4 raw10311step3; decide +kernel
      have hl : raw10311step3Labels = labelEmbedding1 ∘ raw10311step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10311step3 raw10311step3Labels raw10311step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

def raw10312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10312step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10312step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10312 raw10312Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw10312 raw10312Labels = mixedMoment B raw10312step0 raw10312step0Labels := by
      have hz : ∀ j, raw10312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10312step0 = (fun i j => raw10312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10312step0 raw10312; decide +kernel
      have hl : raw10312step0Labels = raw10312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10312 raw10312Labels permutation434 hz
    mixedMoment B raw10312step0 raw10312step0Labels = mixedMoment B raw10312step1 raw10312step1Labels := by
      have hz : ∀ j, raw10312step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10312step1 = (fun i j => raw10312step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10312step1 raw10312step0; decide +kernel
      have hl : raw10312step1Labels = raw10312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10312step0 raw10312step0Labels permutation80 hz
    mixedMoment B raw10312step1 raw10312step1Labels = mixedMoment B raw10312step2 raw10312step2Labels := by
      have ha : raw10312step2 = (fun i j => raw10312step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10312step2 raw10312step1; decide +kernel
      have hl : raw10312step2Labels = raw10312step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10312step1 raw10312step1Labels permutation31 permutation5
    mixedMoment B raw10312step2 raw10312step2Labels = mixedMoment B raw10312step3 raw10312step3Labels := by
      have ha : raw10312step3 = raw10312step2 := by apply Matrix.ext; unfold raw10312step3 raw10312step2; decide +kernel
      have hl : raw10312step2Labels = labelEmbedding8 ∘ raw10312step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10312step2 raw10312step2Labels raw10312step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw10313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10313step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10313step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10313step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10313 raw10313Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw10313 raw10313Labels = mixedMoment B raw10313step0 raw10313step0Labels := by
      have hz : ∀ j, raw10313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10313step0 = (fun i j => raw10313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10313step0 raw10313; decide +kernel
      have hl : raw10313step0Labels = raw10313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10313 raw10313Labels permutation434 hz
    mixedMoment B raw10313step0 raw10313step0Labels = mixedMoment B raw10313step1 raw10313step1Labels := by
      have hz : ∀ j, raw10313step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10313step1 = (fun i j => raw10313step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10313step1 raw10313step0; decide +kernel
      have hl : raw10313step1Labels = raw10313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10313step0 raw10313step0Labels permutation56 hz
    mixedMoment B raw10313step1 raw10313step1Labels = mixedMoment B raw10313step2 raw10313step2Labels := by
      have ha : raw10313step2 = (fun i j => raw10313step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10313step2 raw10313step1; decide +kernel
      have hl : raw10313step2Labels = raw10313step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10313step1 raw10313step1Labels permutation31 permutation5
    mixedMoment B raw10313step2 raw10313step2Labels = mixedMoment B raw10313step3 raw10313step3Labels := by
      have ha : raw10313step3 = raw10313step2 := by apply Matrix.ext; unfold raw10313step3 raw10313step2; decide +kernel
      have hl : raw10313step2Labels = labelEmbedding8 ∘ raw10313step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10313step2 raw10313step2Labels raw10313step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw10314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10314step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10314step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10314step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10314step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10314 raw10314Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw10314 raw10314Labels = mixedMoment B raw10314step0 raw10314step0Labels := by
      have hz : ∀ j, raw10314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10314step0 = (fun i j => raw10314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10314step0 raw10314; decide +kernel
      have hl : raw10314step0Labels = raw10314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10314 raw10314Labels permutation346 hz
    mixedMoment B raw10314step0 raw10314step0Labels = mixedMoment B raw10314step1 raw10314step1Labels := by
      have hz : ∀ j, raw10314step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10314step1 = (fun i j => raw10314step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10314step1 raw10314step0; decide +kernel
      have hl : raw10314step1Labels = raw10314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10314step0 raw10314step0Labels permutation56 hz
    mixedMoment B raw10314step1 raw10314step1Labels = mixedMoment B raw10314step2 raw10314step2Labels := by
      have ha : raw10314step2 = (fun i j => raw10314step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10314step2 raw10314step1; decide +kernel
      have hl : raw10314step2Labels = raw10314step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10314step1 raw10314step1Labels permutation31 permutation5
    mixedMoment B raw10314step2 raw10314step2Labels = mixedMoment B raw10314step3 raw10314step3Labels := by
      have ha : raw10314step3 = raw10314step2 := by apply Matrix.ext; unfold raw10314step3 raw10314step2; decide +kernel
      have hl : raw10314step2Labels = labelEmbedding8 ∘ raw10314step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10314step2 raw10314step2Labels raw10314step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw10315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10315step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, -3, 1]]
def raw10315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10315step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10315step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10315step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10315step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10315 raw10315Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw10315 raw10315Labels = mixedMoment B raw10315step0 raw10315step0Labels := by
      have hz : ∀ j, raw10315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10315step0 = (fun i j => raw10315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10315step0 raw10315; decide +kernel
      have hl : raw10315step0Labels = raw10315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10315 raw10315Labels permutation434 hz
    mixedMoment B raw10315step0 raw10315step0Labels = mixedMoment B raw10315step1 raw10315step1Labels := by
      have hz : ∀ j, raw10315step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10315step1 = (fun i j => raw10315step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10315step1 raw10315step0; decide +kernel
      have hl : raw10315step1Labels = raw10315step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10315step0 raw10315step0Labels permutation80 hz
    mixedMoment B raw10315step1 raw10315step1Labels = mixedMoment B raw10315step2 raw10315step2Labels := by
      have hz : ∀ j, raw10315step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10315step2 = (fun i j => raw10315step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10315step2 raw10315step1; decide +kernel
      have hl : raw10315step2Labels = raw10315step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10315step1 raw10315step1Labels permutation14 hz
    mixedMoment B raw10315step2 raw10315step2Labels = mixedMoment B raw10315step3 raw10315step3Labels := by
      have ha : raw10315step3 = (fun i j => raw10315step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10315step3 raw10315step2; decide +kernel
      have hl : raw10315step3Labels = raw10315step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10315step2 raw10315step2Labels permutation6 permutation5
    mixedMoment B raw10315step3 raw10315step3Labels = mixedMoment B raw10315step4 raw10315step4Labels := by
      have ha : raw10315step4 = raw10315step3 := by apply Matrix.ext; unfold raw10315step4 raw10315step3; decide +kernel
      have hl : raw10315step3Labels = labelEmbedding8 ∘ raw10315step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10315step3 raw10315step3Labels raw10315step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw10316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10316step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw10316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10316step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw10316step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10316 raw10316Labels = mixedMoment B node5494 node5494Labels := by
  calc
    mixedMoment B raw10316 raw10316Labels = mixedMoment B raw10316step0 raw10316step0Labels := by
      have hz : ∀ j, raw10316 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10316step0 = (fun i j => raw10316 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10316step0 raw10316; decide +kernel
      have hl : raw10316step0Labels = raw10316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10316 raw10316Labels permutation434 hz
    mixedMoment B raw10316step0 raw10316step0Labels = mixedMoment B raw10316step1 raw10316step1Labels := by
      have hz : ∀ j, raw10316step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10316step1 = (fun i j => raw10316step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10316step1 raw10316step0; decide +kernel
      have hl : raw10316step1Labels = raw10316step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10316step0 raw10316step0Labels permutation80 hz
    mixedMoment B raw10316step1 raw10316step1Labels = mixedMoment B raw10316step2 raw10316step2Labels := by
      have hz : ∀ j, raw10316step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10316step2 = (fun i j => raw10316step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10316step2 raw10316step1; decide +kernel
      have hl : raw10316step2Labels = raw10316step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10316step1 raw10316step1Labels permutation14 hz
    mixedMoment B raw10316step2 raw10316step2Labels = mixedMoment B raw10316step3 raw10316step3Labels := by
      have ha : raw10316step3 = (fun i j => raw10316step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10316step3 raw10316step2; decide +kernel
      have hl : raw10316step3Labels = raw10316step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10316step2 raw10316step2Labels permutation3 permutation2
    _ = mixedMoment B node5494 node5494Labels := by rfl

def raw10317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10317step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10317step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10317step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10317step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10317 raw10317Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw10317 raw10317Labels = mixedMoment B raw10317step0 raw10317step0Labels := by
      have hz : ∀ j, raw10317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10317step0 = (fun i j => raw10317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10317step0 raw10317; decide +kernel
      have hl : raw10317step0Labels = raw10317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10317 raw10317Labels permutation434 hz
    mixedMoment B raw10317step0 raw10317step0Labels = mixedMoment B raw10317step1 raw10317step1Labels := by
      have hz : ∀ j, raw10317step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10317step1 = (fun i j => raw10317step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10317step1 raw10317step0; decide +kernel
      have hl : raw10317step1Labels = raw10317step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10317step0 raw10317step0Labels permutation80 hz
    mixedMoment B raw10317step1 raw10317step1Labels = mixedMoment B raw10317step2 raw10317step2Labels := by
      have ha : raw10317step2 = (fun i j => raw10317step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10317step2 raw10317step1; decide +kernel
      have hl : raw10317step2Labels = raw10317step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10317step1 raw10317step1Labels permutation10 permutation3
    mixedMoment B raw10317step2 raw10317step2Labels = mixedMoment B raw10317step3 raw10317step3Labels := by
      have ha : raw10317step3 = raw10317step2 := by apply Matrix.ext; unfold raw10317step3 raw10317step2; decide +kernel
      have hl : raw10317step2Labels = labelEmbedding6 ∘ raw10317step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10317step2 raw10317step2Labels raw10317step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw10318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10318step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10318 raw10318Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw10318 raw10318Labels = mixedMoment B raw10318step0 raw10318step0Labels := by
      have hz : ∀ j, raw10318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10318step0 = (fun i j => raw10318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10318step0 raw10318; decide +kernel
      have hl : raw10318step0Labels = raw10318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10318 raw10318Labels permutation434 hz
    mixedMoment B raw10318step0 raw10318step0Labels = mixedMoment B raw10318step1 raw10318step1Labels := by
      have ha : raw10318step1 = (fun i j => raw10318step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10318step1 raw10318step0; decide +kernel
      have hl : raw10318step1Labels = raw10318step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10318step0 raw10318step0Labels permutation40 permutation3
    mixedMoment B raw10318step1 raw10318step1Labels = mixedMoment B raw10318step2 raw10318step2Labels := by
      have ha : raw10318step2 = raw10318step1 := by apply Matrix.ext; unfold raw10318step2 raw10318step1; decide +kernel
      have hl : raw10318step1Labels = labelEmbedding6 ∘ raw10318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10318step1 raw10318step1Labels raw10318step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw10319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10319step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10319 raw10319Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw10319 raw10319Labels = mixedMoment B raw10319step0 raw10319step0Labels := by
      have hz : ∀ j, raw10319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10319step0 = (fun i j => raw10319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10319step0 raw10319; decide +kernel
      have hl : raw10319step0Labels = raw10319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10319 raw10319Labels permutation346 hz
    mixedMoment B raw10319step0 raw10319step0Labels = mixedMoment B raw10319step1 raw10319step1Labels := by
      have ha : raw10319step1 = (fun i j => raw10319step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10319step1 raw10319step0; decide +kernel
      have hl : raw10319step1Labels = raw10319step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10319step0 raw10319step0Labels permutation40 permutation3
    mixedMoment B raw10319step1 raw10319step1Labels = mixedMoment B raw10319step2 raw10319step2Labels := by
      have ha : raw10319step2 = raw10319step1 := by apply Matrix.ext; unfold raw10319step2 raw10319step1; decide +kernel
      have hl : raw10319step1Labels = labelEmbedding6 ∘ raw10319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10319step1 raw10319step1Labels raw10319step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw10320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10320step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10320step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10320step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10320step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10320 raw10320Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw10320 raw10320Labels = mixedMoment B raw10320step0 raw10320step0Labels := by
      have hz : ∀ j, raw10320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10320step0 = (fun i j => raw10320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10320step0 raw10320; decide +kernel
      have hl : raw10320step0Labels = raw10320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10320 raw10320Labels permutation434 hz
    mixedMoment B raw10320step0 raw10320step0Labels = mixedMoment B raw10320step1 raw10320step1Labels := by
      have hz : ∀ j, raw10320step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10320step1 = (fun i j => raw10320step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10320step1 raw10320step0; decide +kernel
      have hl : raw10320step1Labels = raw10320step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10320step0 raw10320step0Labels permutation80 hz
    mixedMoment B raw10320step1 raw10320step1Labels = mixedMoment B raw10320step2 raw10320step2Labels := by
      have ha : raw10320step2 = (fun i j => raw10320step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10320step2 raw10320step1; decide +kernel
      have hl : raw10320step2Labels = raw10320step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10320step1 raw10320step1Labels permutation29 permutation5
    mixedMoment B raw10320step2 raw10320step2Labels = mixedMoment B raw10320step3 raw10320step3Labels := by
      have ha : raw10320step3 = raw10320step2 := by apply Matrix.ext; unfold raw10320step3 raw10320step2; decide +kernel
      have hl : raw10320step2Labels = labelEmbedding8 ∘ raw10320step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10320step2 raw10320step2Labels raw10320step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw10321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10321step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10321step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10321step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10321 raw10321Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw10321 raw10321Labels = mixedMoment B raw10321step0 raw10321step0Labels := by
      have hz : ∀ j, raw10321 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10321step0 = (fun i j => raw10321 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10321step0 raw10321; decide +kernel
      have hl : raw10321step0Labels = raw10321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10321 raw10321Labels permutation434 hz
    mixedMoment B raw10321step0 raw10321step0Labels = mixedMoment B raw10321step1 raw10321step1Labels := by
      have hz : ∀ j, raw10321step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10321step1 = (fun i j => raw10321step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10321step1 raw10321step0; decide +kernel
      have hl : raw10321step1Labels = raw10321step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10321step0 raw10321step0Labels permutation80 hz
    mixedMoment B raw10321step1 raw10321step1Labels = mixedMoment B raw10321step2 raw10321step2Labels := by
      have ha : raw10321step2 = (fun i j => raw10321step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10321step2 raw10321step1; decide +kernel
      have hl : raw10321step2Labels = raw10321step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10321step1 raw10321step1Labels permutation10 permutation3
    mixedMoment B raw10321step2 raw10321step2Labels = mixedMoment B raw10321step3 raw10321step3Labels := by
      have ha : raw10321step3 = raw10321step2 := by apply Matrix.ext; unfold raw10321step3 raw10321step2; decide +kernel
      have hl : raw10321step2Labels = labelEmbedding6 ∘ raw10321step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10321step2 raw10321step2Labels raw10321step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw10322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10322step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10322step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10322 raw10322Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw10322 raw10322Labels = mixedMoment B raw10322step0 raw10322step0Labels := by
      have hz : ∀ j, raw10322 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10322step0 = (fun i j => raw10322 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10322step0 raw10322; decide +kernel
      have hl : raw10322step0Labels = raw10322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10322 raw10322Labels permutation434 hz
    mixedMoment B raw10322step0 raw10322step0Labels = mixedMoment B raw10322step1 raw10322step1Labels := by
      have hz : ∀ j, raw10322step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10322step1 = (fun i j => raw10322step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10322step1 raw10322step0; decide +kernel
      have hl : raw10322step1Labels = raw10322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10322step0 raw10322step0Labels permutation56 hz
    mixedMoment B raw10322step1 raw10322step1Labels = mixedMoment B raw10322step2 raw10322step2Labels := by
      have ha : raw10322step2 = (fun i j => raw10322step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10322step2 raw10322step1; decide +kernel
      have hl : raw10322step2Labels = raw10322step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10322step1 raw10322step1Labels permutation10 permutation3
    mixedMoment B raw10322step2 raw10322step2Labels = mixedMoment B raw10322step3 raw10322step3Labels := by
      have ha : raw10322step3 = raw10322step2 := by apply Matrix.ext; unfold raw10322step3 raw10322step2; decide +kernel
      have hl : raw10322step2Labels = labelEmbedding6 ∘ raw10322step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10322step2 raw10322step2Labels raw10322step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw10323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10323step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10323 raw10323Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw10323 raw10323Labels = mixedMoment B raw10323step0 raw10323step0Labels := by
      have hz : ∀ j, raw10323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10323step0 = (fun i j => raw10323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10323step0 raw10323; decide +kernel
      have hl : raw10323step0Labels = raw10323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10323 raw10323Labels permutation434 hz
    mixedMoment B raw10323step0 raw10323step0Labels = mixedMoment B raw10323step1 raw10323step1Labels := by
      have ha : raw10323step1 = (fun i j => raw10323step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10323step1 raw10323step0; decide +kernel
      have hl : raw10323step1Labels = raw10323step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10323step0 raw10323step0Labels permutation34 permutation3
    mixedMoment B raw10323step1 raw10323step1Labels = mixedMoment B raw10323step2 raw10323step2Labels := by
      have ha : raw10323step2 = raw10323step1 := by apply Matrix.ext; unfold raw10323step2 raw10323step1; decide +kernel
      have hl : raw10323step1Labels = labelEmbedding6 ∘ raw10323step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10323step1 raw10323step1Labels raw10323step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw10324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10324step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10324 raw10324Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw10324 raw10324Labels = mixedMoment B raw10324step0 raw10324step0Labels := by
      have hz : ∀ j, raw10324 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10324step0 = (fun i j => raw10324 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10324step0 raw10324; decide +kernel
      have hl : raw10324step0Labels = raw10324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10324 raw10324Labels permutation265 hz
    mixedMoment B raw10324step0 raw10324step0Labels = mixedMoment B raw10324step1 raw10324step1Labels := by
      have ha : raw10324step1 = (fun i j => raw10324step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10324step1 raw10324step0; decide +kernel
      have hl : raw10324step1Labels = raw10324step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10324step0 raw10324step0Labels permutation40 permutation3
    mixedMoment B raw10324step1 raw10324step1Labels = mixedMoment B raw10324step2 raw10324step2Labels := by
      have ha : raw10324step2 = raw10324step1 := by apply Matrix.ext; unfold raw10324step2 raw10324step1; decide +kernel
      have hl : raw10324step1Labels = labelEmbedding6 ∘ raw10324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10324step1 raw10324step1Labels raw10324step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw10325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10325step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10325step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10325step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10325step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10325step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10325 raw10325Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw10325 raw10325Labels = mixedMoment B raw10325step0 raw10325step0Labels := by
      have hz : ∀ j, raw10325 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10325step0 = (fun i j => raw10325 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10325step0 raw10325; decide +kernel
      have hl : raw10325step0Labels = raw10325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10325 raw10325Labels permutation434 hz
    mixedMoment B raw10325step0 raw10325step0Labels = mixedMoment B raw10325step1 raw10325step1Labels := by
      have hz : ∀ j, raw10325step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10325step1 = (fun i j => raw10325step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10325step1 raw10325step0; decide +kernel
      have hl : raw10325step1Labels = raw10325step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10325step0 raw10325step0Labels permutation56 hz
    mixedMoment B raw10325step1 raw10325step1Labels = mixedMoment B raw10325step2 raw10325step2Labels := by
      have ha : raw10325step2 = (fun i j => raw10325step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10325step2 raw10325step1; decide +kernel
      have hl : raw10325step2Labels = raw10325step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10325step1 raw10325step1Labels permutation29 permutation5
    mixedMoment B raw10325step2 raw10325step2Labels = mixedMoment B raw10325step3 raw10325step3Labels := by
      have ha : raw10325step3 = raw10325step2 := by apply Matrix.ext; unfold raw10325step3 raw10325step2; decide +kernel
      have hl : raw10325step2Labels = labelEmbedding8 ∘ raw10325step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10325step2 raw10325step2Labels raw10325step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw10326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10326step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10326step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10326step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10326 raw10326Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw10326 raw10326Labels = mixedMoment B raw10326step0 raw10326step0Labels := by
      have hz : ∀ j, raw10326 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10326step0 = (fun i j => raw10326 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10326step0 raw10326; decide +kernel
      have hl : raw10326step0Labels = raw10326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10326 raw10326Labels permutation434 hz
    mixedMoment B raw10326step0 raw10326step0Labels = mixedMoment B raw10326step1 raw10326step1Labels := by
      have hz : ∀ j, raw10326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10326step1 = (fun i j => raw10326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10326step1 raw10326step0; decide +kernel
      have hl : raw10326step1Labels = raw10326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10326step0 raw10326step0Labels permutation56 hz
    mixedMoment B raw10326step1 raw10326step1Labels = mixedMoment B raw10326step2 raw10326step2Labels := by
      have ha : raw10326step2 = (fun i j => raw10326step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10326step2 raw10326step1; decide +kernel
      have hl : raw10326step2Labels = raw10326step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10326step1 raw10326step1Labels permutation10 permutation3
    mixedMoment B raw10326step2 raw10326step2Labels = mixedMoment B raw10326step3 raw10326step3Labels := by
      have ha : raw10326step3 = raw10326step2 := by apply Matrix.ext; unfold raw10326step3 raw10326step2; decide +kernel
      have hl : raw10326step2Labels = labelEmbedding6 ∘ raw10326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10326step2 raw10326step2Labels raw10326step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw10327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10327step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10327step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10327 raw10327Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw10327 raw10327Labels = mixedMoment B raw10327step0 raw10327step0Labels := by
      have hz : ∀ j, raw10327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10327step0 = (fun i j => raw10327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10327step0 raw10327; decide +kernel
      have hl : raw10327step0Labels = raw10327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10327 raw10327Labels permutation346 hz
    mixedMoment B raw10327step0 raw10327step0Labels = mixedMoment B raw10327step1 raw10327step1Labels := by
      have hz : ∀ j, raw10327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10327step1 = (fun i j => raw10327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10327step1 raw10327step0; decide +kernel
      have hl : raw10327step1Labels = raw10327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10327step0 raw10327step0Labels permutation56 hz
    mixedMoment B raw10327step1 raw10327step1Labels = mixedMoment B raw10327step2 raw10327step2Labels := by
      have ha : raw10327step2 = (fun i j => raw10327step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10327step2 raw10327step1; decide +kernel
      have hl : raw10327step2Labels = raw10327step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10327step1 raw10327step1Labels permutation10 permutation3
    mixedMoment B raw10327step2 raw10327step2Labels = mixedMoment B raw10327step3 raw10327step3Labels := by
      have ha : raw10327step3 = raw10327step2 := by apply Matrix.ext; unfold raw10327step3 raw10327step2; decide +kernel
      have hl : raw10327step2Labels = labelEmbedding6 ∘ raw10327step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10327step2 raw10327step2Labels raw10327step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw10328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10328step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10328step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10328 raw10328Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw10328 raw10328Labels = mixedMoment B raw10328step0 raw10328step0Labels := by
      have hz : ∀ j, raw10328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10328step0 = (fun i j => raw10328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10328step0 raw10328; decide +kernel
      have hl : raw10328step0Labels = raw10328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10328 raw10328Labels permutation346 hz
    mixedMoment B raw10328step0 raw10328step0Labels = mixedMoment B raw10328step1 raw10328step1Labels := by
      have ha : raw10328step1 = (fun i j => raw10328step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10328step1 raw10328step0; decide +kernel
      have hl : raw10328step1Labels = raw10328step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10328step0 raw10328step0Labels permutation34 permutation3
    mixedMoment B raw10328step1 raw10328step1Labels = mixedMoment B raw10328step2 raw10328step2Labels := by
      have ha : raw10328step2 = raw10328step1 := by apply Matrix.ext; unfold raw10328step2 raw10328step1; decide +kernel
      have hl : raw10328step1Labels = labelEmbedding6 ∘ raw10328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10328step1 raw10328step1Labels raw10328step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw10329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10329step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10329step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10329 raw10329Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw10329 raw10329Labels = mixedMoment B raw10329step0 raw10329step0Labels := by
      have hz : ∀ j, raw10329 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10329step0 = (fun i j => raw10329 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10329step0 raw10329; decide +kernel
      have hl : raw10329step0Labels = raw10329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10329 raw10329Labels permutation265 hz
    mixedMoment B raw10329step0 raw10329step0Labels = mixedMoment B raw10329step1 raw10329step1Labels := by
      have ha : raw10329step1 = (fun i j => raw10329step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10329step1 raw10329step0; decide +kernel
      have hl : raw10329step1Labels = raw10329step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10329step0 raw10329step0Labels permutation34 permutation3
    mixedMoment B raw10329step1 raw10329step1Labels = mixedMoment B raw10329step2 raw10329step2Labels := by
      have ha : raw10329step2 = raw10329step1 := by apply Matrix.ext; unfold raw10329step2 raw10329step1; decide +kernel
      have hl : raw10329step1Labels = labelEmbedding6 ∘ raw10329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10329step1 raw10329step1Labels raw10329step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw10330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10330step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10330step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10330 raw10330Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw10330 raw10330Labels = mixedMoment B raw10330step0 raw10330step0Labels := by
      have hz : ∀ j, raw10330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10330step0 = (fun i j => raw10330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10330step0 raw10330; decide +kernel
      have hl : raw10330step0Labels = raw10330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10330 raw10330Labels permutation346 hz
    mixedMoment B raw10330step0 raw10330step0Labels = mixedMoment B raw10330step1 raw10330step1Labels := by
      have hz : ∀ j, raw10330step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10330step1 = (fun i j => raw10330step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10330step1 raw10330step0; decide +kernel
      have hl : raw10330step1Labels = raw10330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10330step0 raw10330step0Labels permutation56 hz
    mixedMoment B raw10330step1 raw10330step1Labels = mixedMoment B raw10330step2 raw10330step2Labels := by
      have ha : raw10330step2 = (fun i j => raw10330step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10330step2 raw10330step1; decide +kernel
      have hl : raw10330step2Labels = raw10330step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10330step1 raw10330step1Labels permutation29 permutation5
    mixedMoment B raw10330step2 raw10330step2Labels = mixedMoment B raw10330step3 raw10330step3Labels := by
      have ha : raw10330step3 = raw10330step2 := by apply Matrix.ext; unfold raw10330step3 raw10330step2; decide +kernel
      have hl : raw10330step2Labels = labelEmbedding8 ∘ raw10330step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10330step2 raw10330step2Labels raw10330step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw10331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10331step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10331step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10331step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10331 raw10331Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw10331 raw10331Labels = mixedMoment B raw10331step0 raw10331step0Labels := by
      have hz : ∀ j, raw10331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10331step0 = (fun i j => raw10331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10331step0 raw10331; decide +kernel
      have hl : raw10331step0Labels = raw10331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10331 raw10331Labels permutation346 hz
    mixedMoment B raw10331step0 raw10331step0Labels = mixedMoment B raw10331step1 raw10331step1Labels := by
      have hz : ∀ j, raw10331step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10331step1 = (fun i j => raw10331step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10331step1 raw10331step0; decide +kernel
      have hl : raw10331step1Labels = raw10331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10331step0 raw10331step0Labels permutation56 hz
    mixedMoment B raw10331step1 raw10331step1Labels = mixedMoment B raw10331step2 raw10331step2Labels := by
      have ha : raw10331step2 = (fun i j => raw10331step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10331step2 raw10331step1; decide +kernel
      have hl : raw10331step2Labels = raw10331step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10331step1 raw10331step1Labels permutation10 permutation3
    mixedMoment B raw10331step2 raw10331step2Labels = mixedMoment B raw10331step3 raw10331step3Labels := by
      have ha : raw10331step3 = raw10331step2 := by apply Matrix.ext; unfold raw10331step3 raw10331step2; decide +kernel
      have hl : raw10331step2Labels = labelEmbedding6 ∘ raw10331step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10331step2 raw10331step2Labels raw10331step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw10332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10332step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, 0, -2], ![2, -3, 1]]
def raw10332step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10332step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw10332step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10332step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw10332step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10332 raw10332Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw10332 raw10332Labels = mixedMoment B raw10332step0 raw10332step0Labels := by
      have hz : ∀ j, raw10332 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10332step0 = (fun i j => raw10332 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10332step0 raw10332; decide +kernel
      have hl : raw10332step0Labels = raw10332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10332 raw10332Labels permutation434 hz
    mixedMoment B raw10332step0 raw10332step0Labels = mixedMoment B raw10332step1 raw10332step1Labels := by
      have hz : ∀ j, raw10332step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10332step1 = (fun i j => raw10332step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10332step1 raw10332step0; decide +kernel
      have hl : raw10332step1Labels = raw10332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10332step0 raw10332step0Labels permutation80 hz
    mixedMoment B raw10332step1 raw10332step1Labels = mixedMoment B raw10332step2 raw10332step2Labels := by
      have hz : ∀ j, raw10332step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10332step2 = (fun i j => raw10332step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10332step2 raw10332step1; decide +kernel
      have hl : raw10332step2Labels = raw10332step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10332step1 raw10332step1Labels permutation14 hz
    mixedMoment B raw10332step2 raw10332step2Labels = mixedMoment B raw10332step3 raw10332step3Labels := by
      have ha : raw10332step3 = (fun i j => raw10332step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10332step3 raw10332step2; decide +kernel
      have hl : raw10332step3Labels = raw10332step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10332step2 raw10332step2Labels permutation2 permutation3
    mixedMoment B raw10332step3 raw10332step3Labels = mixedMoment B raw10332step4 raw10332step4Labels := by
      have ha : raw10332step4 = raw10332step3 := by apply Matrix.ext; unfold raw10332step4 raw10332step3; decide +kernel
      have hl : raw10332step3Labels = labelEmbedding6 ∘ raw10332step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10332step3 raw10332step3Labels raw10332step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw10333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10333step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10333step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10333 raw10333Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw10333 raw10333Labels = mixedMoment B raw10333step0 raw10333step0Labels := by
      have hz : ∀ j, raw10333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10333step0 = (fun i j => raw10333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10333step0 raw10333; decide +kernel
      have hl : raw10333step0Labels = raw10333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10333 raw10333Labels permutation434 hz
    mixedMoment B raw10333step0 raw10333step0Labels = mixedMoment B raw10333step1 raw10333step1Labels := by
      have hz : ∀ j, raw10333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10333step1 = (fun i j => raw10333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10333step1 raw10333step0; decide +kernel
      have hl : raw10333step1Labels = raw10333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10333step0 raw10333step0Labels permutation80 hz
    mixedMoment B raw10333step1 raw10333step1Labels = mixedMoment B raw10333step2 raw10333step2Labels := by
      have ha : raw10333step2 = (fun i j => raw10333step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10333step2 raw10333step1; decide +kernel
      have hl : raw10333step2Labels = raw10333step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10333step1 raw10333step1Labels permutation8 permutation3
    mixedMoment B raw10333step2 raw10333step2Labels = mixedMoment B raw10333step3 raw10333step3Labels := by
      have ha : raw10333step3 = raw10333step2 := by apply Matrix.ext; unfold raw10333step3 raw10333step2; decide +kernel
      have hl : raw10333step2Labels = labelEmbedding6 ∘ raw10333step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10333step2 raw10333step2Labels raw10333step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw10334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10334step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10334step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10334 raw10334Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw10334 raw10334Labels = mixedMoment B raw10334step0 raw10334step0Labels := by
      have hz : ∀ j, raw10334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10334step0 = (fun i j => raw10334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10334step0 raw10334; decide +kernel
      have hl : raw10334step0Labels = raw10334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10334 raw10334Labels permutation434 hz
    mixedMoment B raw10334step0 raw10334step0Labels = mixedMoment B raw10334step1 raw10334step1Labels := by
      have hz : ∀ j, raw10334step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10334step1 = (fun i j => raw10334step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10334step1 raw10334step0; decide +kernel
      have hl : raw10334step1Labels = raw10334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10334step0 raw10334step0Labels permutation56 hz
    mixedMoment B raw10334step1 raw10334step1Labels = mixedMoment B raw10334step2 raw10334step2Labels := by
      have ha : raw10334step2 = (fun i j => raw10334step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10334step2 raw10334step1; decide +kernel
      have hl : raw10334step2Labels = raw10334step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10334step1 raw10334step1Labels permutation8 permutation3
    mixedMoment B raw10334step2 raw10334step2Labels = mixedMoment B raw10334step3 raw10334step3Labels := by
      have ha : raw10334step3 = raw10334step2 := by apply Matrix.ext; unfold raw10334step3 raw10334step2; decide +kernel
      have hl : raw10334step2Labels = labelEmbedding6 ∘ raw10334step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10334step2 raw10334step2Labels raw10334step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw10335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10335step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10335step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10335step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10335 raw10335Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw10335 raw10335Labels = mixedMoment B raw10335step0 raw10335step0Labels := by
      have hz : ∀ j, raw10335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10335step0 = (fun i j => raw10335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10335step0 raw10335; decide +kernel
      have hl : raw10335step0Labels = raw10335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10335 raw10335Labels permutation346 hz
    mixedMoment B raw10335step0 raw10335step0Labels = mixedMoment B raw10335step1 raw10335step1Labels := by
      have hz : ∀ j, raw10335step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10335step1 = (fun i j => raw10335step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10335step1 raw10335step0; decide +kernel
      have hl : raw10335step1Labels = raw10335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10335step0 raw10335step0Labels permutation56 hz
    mixedMoment B raw10335step1 raw10335step1Labels = mixedMoment B raw10335step2 raw10335step2Labels := by
      have ha : raw10335step2 = (fun i j => raw10335step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10335step2 raw10335step1; decide +kernel
      have hl : raw10335step2Labels = raw10335step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10335step1 raw10335step1Labels permutation8 permutation3
    mixedMoment B raw10335step2 raw10335step2Labels = mixedMoment B raw10335step3 raw10335step3Labels := by
      have ha : raw10335step3 = raw10335step2 := by apply Matrix.ext; unfold raw10335step3 raw10335step2; decide +kernel
      have hl : raw10335step2Labels = labelEmbedding6 ∘ raw10335step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10335step2 raw10335step2Labels raw10335step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw10336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw10336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw10336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw10336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10336step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![2, 0, -2], ![1, -2, 1]]
def raw10336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10336step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10336step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10336step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10336step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10336 raw10336Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw10336 raw10336Labels = mixedMoment B raw10336step0 raw10336step0Labels := by
      have hz : ∀ j, raw10336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10336step0 = (fun i j => raw10336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10336step0 raw10336; decide +kernel
      have hl : raw10336step0Labels = raw10336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10336 raw10336Labels permutation434 hz
    mixedMoment B raw10336step0 raw10336step0Labels = mixedMoment B raw10336step1 raw10336step1Labels := by
      have hz : ∀ j, raw10336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10336step1 = (fun i j => raw10336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10336step1 raw10336step0; decide +kernel
      have hl : raw10336step1Labels = raw10336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10336step0 raw10336step0Labels permutation80 hz
    mixedMoment B raw10336step1 raw10336step1Labels = mixedMoment B raw10336step2 raw10336step2Labels := by
      have hz : ∀ j, raw10336step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10336step2 = (fun i j => raw10336step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10336step2 raw10336step1; decide +kernel
      have hl : raw10336step2Labels = raw10336step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10336step1 raw10336step1Labels permutation14 hz
    mixedMoment B raw10336step2 raw10336step2Labels = mixedMoment B raw10336step3 raw10336step3Labels := by
      have ha : raw10336step3 = (fun i j => raw10336step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10336step3 raw10336step2; decide +kernel
      have hl : raw10336step3Labels = raw10336step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10336step2 raw10336step2Labels permutation3 permutation3
    mixedMoment B raw10336step3 raw10336step3Labels = mixedMoment B raw10336step4 raw10336step4Labels := by
      have ha : raw10336step4 = raw10336step3 := by apply Matrix.ext; unfold raw10336step4 raw10336step3; decide +kernel
      have hl : raw10336step3Labels = labelEmbedding6 ∘ raw10336step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10336step3 raw10336step3Labels raw10336step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw10337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10337step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw10337step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10337step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw10337step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10337step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw10337step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10337 raw10337Labels = mixedMoment B node4493 node4493Labels := by
  calc
    mixedMoment B raw10337 raw10337Labels = mixedMoment B raw10337step0 raw10337step0Labels := by
      have hz : ∀ j, raw10337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10337step0 = (fun i j => raw10337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10337step0 raw10337; decide +kernel
      have hl : raw10337step0Labels = raw10337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10337 raw10337Labels permutation434 hz
    mixedMoment B raw10337step0 raw10337step0Labels = mixedMoment B raw10337step1 raw10337step1Labels := by
      have hz : ∀ j, raw10337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10337step1 = (fun i j => raw10337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10337step1 raw10337step0; decide +kernel
      have hl : raw10337step1Labels = raw10337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10337step0 raw10337step0Labels permutation80 hz
    mixedMoment B raw10337step1 raw10337step1Labels = mixedMoment B raw10337step2 raw10337step2Labels := by
      have hz : ∀ j, raw10337step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10337step2 = (fun i j => raw10337step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10337step2 raw10337step1; decide +kernel
      have hl : raw10337step2Labels = raw10337step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10337step1 raw10337step1Labels permutation14 hz
    mixedMoment B raw10337step2 raw10337step2Labels = mixedMoment B raw10337step3 raw10337step3Labels := by
      have ha : raw10337step3 = (fun i j => raw10337step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10337step3 raw10337step2; decide +kernel
      have hl : raw10337step3Labels = raw10337step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10337step2 raw10337step2Labels permutation2 permutation3
    mixedMoment B raw10337step3 raw10337step3Labels = mixedMoment B raw10337step4 raw10337step4Labels := by
      have ha : raw10337step4 = raw10337step3 := by apply Matrix.ext; unfold raw10337step4 raw10337step3; decide +kernel
      have hl : raw10337step3Labels = labelEmbedding6 ∘ raw10337step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10337step3 raw10337step3Labels raw10337step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4493 node4493Labels := by rfl

def raw10338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10338step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10338step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10338step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10338 raw10338Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw10338 raw10338Labels = mixedMoment B raw10338step0 raw10338step0Labels := by
      have hz : ∀ j, raw10338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10338step0 = (fun i j => raw10338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10338step0 raw10338; decide +kernel
      have hl : raw10338step0Labels = raw10338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10338 raw10338Labels permutation434 hz
    mixedMoment B raw10338step0 raw10338step0Labels = mixedMoment B raw10338step1 raw10338step1Labels := by
      have hz : ∀ j, raw10338step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10338step1 = (fun i j => raw10338step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10338step1 raw10338step0; decide +kernel
      have hl : raw10338step1Labels = raw10338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10338step0 raw10338step0Labels permutation80 hz
    mixedMoment B raw10338step1 raw10338step1Labels = mixedMoment B raw10338step2 raw10338step2Labels := by
      have ha : raw10338step2 = (fun i j => raw10338step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10338step2 raw10338step1; decide +kernel
      have hl : raw10338step2Labels = raw10338step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10338step1 raw10338step1Labels permutation31 permutation5
    mixedMoment B raw10338step2 raw10338step2Labels = mixedMoment B raw10338step3 raw10338step3Labels := by
      have ha : raw10338step3 = raw10338step2 := by apply Matrix.ext; unfold raw10338step3 raw10338step2; decide +kernel
      have hl : raw10338step2Labels = labelEmbedding8 ∘ raw10338step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10338step2 raw10338step2Labels raw10338step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw10339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10339step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10339step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10339step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10339step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10339 raw10339Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw10339 raw10339Labels = mixedMoment B raw10339step0 raw10339step0Labels := by
      have hz : ∀ j, raw10339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10339step0 = (fun i j => raw10339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10339step0 raw10339; decide +kernel
      have hl : raw10339step0Labels = raw10339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10339 raw10339Labels permutation434 hz
    mixedMoment B raw10339step0 raw10339step0Labels = mixedMoment B raw10339step1 raw10339step1Labels := by
      have hz : ∀ j, raw10339step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10339step1 = (fun i j => raw10339step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10339step1 raw10339step0; decide +kernel
      have hl : raw10339step1Labels = raw10339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10339step0 raw10339step0Labels permutation56 hz
    mixedMoment B raw10339step1 raw10339step1Labels = mixedMoment B raw10339step2 raw10339step2Labels := by
      have ha : raw10339step2 = (fun i j => raw10339step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10339step2 raw10339step1; decide +kernel
      have hl : raw10339step2Labels = raw10339step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10339step1 raw10339step1Labels permutation31 permutation5
    mixedMoment B raw10339step2 raw10339step2Labels = mixedMoment B raw10339step3 raw10339step3Labels := by
      have ha : raw10339step3 = raw10339step2 := by apply Matrix.ext; unfold raw10339step3 raw10339step2; decide +kernel
      have hl : raw10339step2Labels = labelEmbedding8 ∘ raw10339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10339step2 raw10339step2Labels raw10339step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw10340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10340step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10340step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10340step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10340 raw10340Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw10340 raw10340Labels = mixedMoment B raw10340step0 raw10340step0Labels := by
      have hz : ∀ j, raw10340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10340step0 = (fun i j => raw10340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10340step0 raw10340; decide +kernel
      have hl : raw10340step0Labels = raw10340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10340 raw10340Labels permutation346 hz
    mixedMoment B raw10340step0 raw10340step0Labels = mixedMoment B raw10340step1 raw10340step1Labels := by
      have hz : ∀ j, raw10340step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10340step1 = (fun i j => raw10340step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10340step1 raw10340step0; decide +kernel
      have hl : raw10340step1Labels = raw10340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10340step0 raw10340step0Labels permutation56 hz
    mixedMoment B raw10340step1 raw10340step1Labels = mixedMoment B raw10340step2 raw10340step2Labels := by
      have ha : raw10340step2 = (fun i j => raw10340step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10340step2 raw10340step1; decide +kernel
      have hl : raw10340step2Labels = raw10340step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10340step1 raw10340step1Labels permutation31 permutation5
    mixedMoment B raw10340step2 raw10340step2Labels = mixedMoment B raw10340step3 raw10340step3Labels := by
      have ha : raw10340step3 = raw10340step2 := by apply Matrix.ext; unfold raw10340step3 raw10340step2; decide +kernel
      have hl : raw10340step2Labels = labelEmbedding8 ∘ raw10340step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10340step2 raw10340step2Labels raw10340step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw10341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -4, 1]]
def raw10341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -4, 1]]
def raw10341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 2, -2], ![3, -4, 1]]
def raw10341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10341step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![3, -4, 1]]
def raw10341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10341step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw10341step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10341step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw10341step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10341 raw10341Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw10341 raw10341Labels = mixedMoment B raw10341step0 raw10341step0Labels := by
      have hz : ∀ j, raw10341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10341step0 = (fun i j => raw10341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10341step0 raw10341; decide +kernel
      have hl : raw10341step0Labels = raw10341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10341 raw10341Labels permutation434 hz
    mixedMoment B raw10341step0 raw10341step0Labels = mixedMoment B raw10341step1 raw10341step1Labels := by
      have hz : ∀ j, raw10341step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10341step1 = (fun i j => raw10341step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10341step1 raw10341step0; decide +kernel
      have hl : raw10341step1Labels = raw10341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10341step0 raw10341step0Labels permutation80 hz
    mixedMoment B raw10341step1 raw10341step1Labels = mixedMoment B raw10341step2 raw10341step2Labels := by
      have hz : ∀ j, raw10341step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10341step2 = (fun i j => raw10341step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10341step2 raw10341step1; decide +kernel
      have hl : raw10341step2Labels = raw10341step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10341step1 raw10341step1Labels permutation14 hz
    mixedMoment B raw10341step2 raw10341step2Labels = mixedMoment B raw10341step3 raw10341step3Labels := by
      have ha : raw10341step3 = (fun i j => raw10341step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10341step3 raw10341step2; decide +kernel
      have hl : raw10341step3Labels = raw10341step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10341step2 raw10341step2Labels permutation7 permutation5
    mixedMoment B raw10341step3 raw10341step3Labels = mixedMoment B raw10341step4 raw10341step4Labels := by
      have ha : raw10341step4 = raw10341step3 := by apply Matrix.ext; unfold raw10341step4 raw10341step3; decide +kernel
      have hl : raw10341step3Labels = labelEmbedding8 ∘ raw10341step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10341step3 raw10341step3Labels raw10341step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw10342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10342 raw10342Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw10342 raw10342Labels = mixedMoment B raw10342step0 raw10342step0Labels := by
      have hz : ∀ j, raw10342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10342step0 = (fun i j => raw10342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10342step0 raw10342; decide +kernel
      have hl : raw10342step0Labels = raw10342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10342 raw10342Labels permutation346 hz
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw10343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10343 raw10343Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw10343 raw10343Labels = mixedMoment B raw10343step0 raw10343step0Labels := by
      have hz : ∀ j, raw10343 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10343step0 = (fun i j => raw10343 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10343step0 raw10343; decide +kernel
      have hl : raw10343step0Labels = raw10343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10343 raw10343Labels permutation265 hz
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw10344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10344 raw10344Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw10344 raw10344Labels = mixedMoment B raw10344step0 raw10344step0Labels := by
      have hz : ∀ j, raw10344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10344step0 = (fun i j => raw10344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10344step0 raw10344; decide +kernel
      have hl : raw10344step0Labels = raw10344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10344 raw10344Labels permutation346 hz
    mixedMoment B raw10344step0 raw10344step0Labels = mixedMoment B raw10344step1 raw10344step1Labels := by
      have hz : ∀ j, raw10344step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10344step1 = (fun i j => raw10344step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10344step1 raw10344step0; decide +kernel
      have hl : raw10344step1Labels = raw10344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10344step0 raw10344step0Labels permutation56 hz
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw10345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10345step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10345step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10345step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10345step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10345step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10345 raw10345Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw10345 raw10345Labels = mixedMoment B raw10345step0 raw10345step0Labels := by
      have hz : ∀ j, raw10345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10345step0 = (fun i j => raw10345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10345step0 raw10345; decide +kernel
      have hl : raw10345step0Labels = raw10345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10345 raw10345Labels permutation346 hz
    mixedMoment B raw10345step0 raw10345step0Labels = mixedMoment B raw10345step1 raw10345step1Labels := by
      have hz : ∀ j, raw10345step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10345step1 = (fun i j => raw10345step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10345step1 raw10345step0; decide +kernel
      have hl : raw10345step1Labels = raw10345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10345step0 raw10345step0Labels permutation56 hz
    mixedMoment B raw10345step1 raw10345step1Labels = mixedMoment B raw10345step2 raw10345step2Labels := by
      have ha : raw10345step2 = (fun i j => raw10345step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10345step2 raw10345step1; decide +kernel
      have hl : raw10345step2Labels = raw10345step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10345step1 raw10345step1Labels permutation9 permutation7
    mixedMoment B raw10345step2 raw10345step2Labels = mixedMoment B raw10345step3 raw10345step3Labels := by
      have ha : raw10345step3 = -raw10345step2 := by apply Matrix.ext; change ∀ i j, raw10345step3 i j = -(raw10345step2 i j); unfold raw10345step3 raw10345step2; decide +kernel
      have hl : raw10345step3Labels = raw10345step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10345step3 raw10345step3Labels = mixedMoment B raw10345step4 raw10345step4Labels := by
      have ha : raw10345step4 = raw10345step3 := by apply Matrix.ext; unfold raw10345step4 raw10345step3; decide +kernel
      have hl : raw10345step3Labels = labelEmbedding10 ∘ raw10345step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10345step3 raw10345step3Labels raw10345step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw10346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw10346step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10346step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10346step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10346step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10346step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10346 raw10346Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw10346 raw10346Labels = mixedMoment B raw10346step0 raw10346step0Labels := by
      have hz : ∀ j, raw10346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10346step0 = (fun i j => raw10346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10346step0 raw10346; decide +kernel
      have hl : raw10346step0Labels = raw10346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10346 raw10346Labels permutation346 hz
    mixedMoment B raw10346step0 raw10346step0Labels = mixedMoment B raw10346step1 raw10346step1Labels := by
      have hz : ∀ j, raw10346step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10346step1 = (fun i j => raw10346step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10346step1 raw10346step0; decide +kernel
      have hl : raw10346step1Labels = raw10346step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10346step0 raw10346step0Labels permutation56 hz
    mixedMoment B raw10346step1 raw10346step1Labels = mixedMoment B raw10346step2 raw10346step2Labels := by
      have ha : raw10346step2 = (fun i j => raw10346step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10346step2 raw10346step1; decide +kernel
      have hl : raw10346step2Labels = raw10346step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10346step1 raw10346step1Labels permutation9 permutation7
    mixedMoment B raw10346step2 raw10346step2Labels = mixedMoment B raw10346step3 raw10346step3Labels := by
      have ha : raw10346step3 = -raw10346step2 := by apply Matrix.ext; change ∀ i j, raw10346step3 i j = -(raw10346step2 i j); unfold raw10346step3 raw10346step2; decide +kernel
      have hl : raw10346step3Labels = raw10346step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10346step3 raw10346step3Labels = mixedMoment B raw10346step4 raw10346step4Labels := by
      have ha : raw10346step4 = raw10346step3 := by apply Matrix.ext; unfold raw10346step4 raw10346step3; decide +kernel
      have hl : raw10346step3Labels = labelEmbedding10 ∘ raw10346step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10346step3 raw10346step3Labels raw10346step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw10347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10347 raw10347Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw10347 raw10347Labels = mixedMoment B raw10347step0 raw10347step0Labels := by
      have hz : ∀ j, raw10347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10347step0 = (fun i j => raw10347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10347step0 raw10347; decide +kernel
      have hl : raw10347step0Labels = raw10347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10347 raw10347Labels permutation346 hz
    mixedMoment B raw10347step0 raw10347step0Labels = mixedMoment B raw10347step1 raw10347step1Labels := by
      have ha : raw10347step1 = (fun i j => raw10347step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10347step1 raw10347step0; decide +kernel
      have hl : raw10347step1Labels = raw10347step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10347step0 raw10347step0Labels permutation38 permutation2
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw10348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10348 raw10348Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw10348 raw10348Labels = mixedMoment B raw10348step0 raw10348step0Labels := by
      have ha : raw10348step0 = (fun i j => raw10348 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10348step0 raw10348; decide +kernel
      have hl : raw10348step0Labels = raw10348Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10348 raw10348Labels permutation182 permutation2
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw10349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10349 raw10349Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw10349 raw10349Labels = mixedMoment B raw10349step0 raw10349step0Labels := by
      have hz : ∀ j, raw10349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10349step0 = (fun i j => raw10349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10349step0 raw10349; decide +kernel
      have hl : raw10349step0Labels = raw10349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10349 raw10349Labels permutation346 hz
    mixedMoment B raw10349step0 raw10349step0Labels = mixedMoment B raw10349step1 raw10349step1Labels := by
      have ha : raw10349step1 = (fun i j => raw10349step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10349step1 raw10349step0; decide +kernel
      have hl : raw10349step1Labels = raw10349step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10349step0 raw10349step0Labels permutation38 permutation2
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw10350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10350 raw10350Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw10350 raw10350Labels = mixedMoment B raw10350step0 raw10350step0Labels := by
      have hz : ∀ j, raw10350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10350step0 = (fun i j => raw10350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10350step0 raw10350; decide +kernel
      have hl : raw10350step0Labels = raw10350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10350 raw10350Labels permutation346 hz
    mixedMoment B raw10350step0 raw10350step0Labels = mixedMoment B raw10350step1 raw10350step1Labels := by
      have ha : raw10350step1 = (fun i j => raw10350step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10350step1 raw10350step0; decide +kernel
      have hl : raw10350step1Labels = raw10350step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10350step0 raw10350step0Labels permutation40 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw10351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10351 raw10351Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10351 raw10351Labels = mixedMoment B raw10351step0 raw10351step0Labels := by
      have hz : ∀ j, raw10351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10351step0 = (fun i j => raw10351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10351step0 raw10351; decide +kernel
      have hl : raw10351step0Labels = raw10351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10351 raw10351Labels permutation346 hz
    mixedMoment B raw10351step0 raw10351step0Labels = mixedMoment B raw10351step1 raw10351step1Labels := by
      have ha : raw10351step1 = (fun i j => raw10351step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10351step1 raw10351step0; decide +kernel
      have hl : raw10351step1Labels = raw10351step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10351step0 raw10351step0Labels permutation39 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10352 raw10352Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw10352 raw10352Labels = mixedMoment B raw10352step0 raw10352step0Labels := by
      have hz : ∀ j, raw10352 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10352step0 = (fun i j => raw10352 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10352step0 raw10352; decide +kernel
      have hl : raw10352step0Labels = raw10352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10352 raw10352Labels permutation265 hz
    mixedMoment B raw10352step0 raw10352step0Labels = mixedMoment B raw10352step1 raw10352step1Labels := by
      have ha : raw10352step1 = (fun i j => raw10352step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10352step1 raw10352step0; decide +kernel
      have hl : raw10352step1Labels = raw10352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10352step0 raw10352step0Labels permutation38 permutation2
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw10353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10353 raw10353Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw10353 raw10353Labels = mixedMoment B raw10353step0 raw10353step0Labels := by
      have ha : raw10353step0 = (fun i j => raw10353 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10353step0 raw10353; decide +kernel
      have hl : raw10353step0Labels = raw10353Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10353 raw10353Labels permutation158 permutation2
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw10354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10354 raw10354Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw10354 raw10354Labels = mixedMoment B raw10354step0 raw10354step0Labels := by
      have hz : ∀ j, raw10354 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10354step0 = (fun i j => raw10354 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10354step0 raw10354; decide +kernel
      have hl : raw10354step0Labels = raw10354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10354 raw10354Labels permutation265 hz
    mixedMoment B raw10354step0 raw10354step0Labels = mixedMoment B raw10354step1 raw10354step1Labels := by
      have ha : raw10354step1 = (fun i j => raw10354step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10354step1 raw10354step0; decide +kernel
      have hl : raw10354step1Labels = raw10354step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10354step0 raw10354step0Labels permutation38 permutation2
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw10355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10355 raw10355Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw10355 raw10355Labels = mixedMoment B raw10355step0 raw10355step0Labels := by
      have hz : ∀ j, raw10355 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10355step0 = (fun i j => raw10355 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10355step0 raw10355; decide +kernel
      have hl : raw10355step0Labels = raw10355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10355 raw10355Labels permutation265 hz
    mixedMoment B raw10355step0 raw10355step0Labels = mixedMoment B raw10355step1 raw10355step1Labels := by
      have ha : raw10355step1 = (fun i j => raw10355step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10355step1 raw10355step0; decide +kernel
      have hl : raw10355step1Labels = raw10355step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10355step0 raw10355step0Labels permutation40 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw10356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10356 raw10356Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10356 raw10356Labels = mixedMoment B raw10356step0 raw10356step0Labels := by
      have hz : ∀ j, raw10356 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10356step0 = (fun i j => raw10356 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10356step0 raw10356; decide +kernel
      have hl : raw10356step0Labels = raw10356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10356 raw10356Labels permutation265 hz
    mixedMoment B raw10356step0 raw10356step0Labels = mixedMoment B raw10356step1 raw10356step1Labels := by
      have ha : raw10356step1 = (fun i j => raw10356step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10356step1 raw10356step0; decide +kernel
      have hl : raw10356step1Labels = raw10356step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10356step0 raw10356step0Labels permutation39 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10357step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10357 raw10357Labels = mixedMoment B node4620 node4620Labels := by
  calc
    mixedMoment B raw10357 raw10357Labels = mixedMoment B raw10357step0 raw10357step0Labels := by
      have hz : ∀ j, raw10357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10357step0 = (fun i j => raw10357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10357step0 raw10357; decide +kernel
      have hl : raw10357step0Labels = raw10357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10357 raw10357Labels permutation346 hz
    mixedMoment B raw10357step0 raw10357step0Labels = mixedMoment B raw10357step1 raw10357step1Labels := by
      have hz : ∀ j, raw10357step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10357step1 = (fun i j => raw10357step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10357step1 raw10357step0; decide +kernel
      have hl : raw10357step1Labels = raw10357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10357step0 raw10357step0Labels permutation56 hz
    _ = mixedMoment B node4620 node4620Labels := by rfl

def raw10358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10358 raw10358Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw10358 raw10358Labels = mixedMoment B raw10358step0 raw10358step0Labels := by
      have hz : ∀ j, raw10358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10358step0 = (fun i j => raw10358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10358step0 raw10358; decide +kernel
      have hl : raw10358step0Labels = raw10358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10358 raw10358Labels permutation346 hz
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw10359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10359 raw10359Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw10359 raw10359Labels = mixedMoment B raw10359step0 raw10359step0Labels := by
      have hz : ∀ j, raw10359 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10359step0 = (fun i j => raw10359 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10359step0 raw10359; decide +kernel
      have hl : raw10359step0Labels = raw10359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10359 raw10359Labels permutation265 hz
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw10360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw10360step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10360 raw10360Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw10360 raw10360Labels = mixedMoment B raw10360step0 raw10360step0Labels := by
      have hz : ∀ j, raw10360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10360step0 = (fun i j => raw10360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10360step0 raw10360; decide +kernel
      have hl : raw10360step0Labels = raw10360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10360 raw10360Labels permutation346 hz
    mixedMoment B raw10360step0 raw10360step0Labels = mixedMoment B raw10360step1 raw10360step1Labels := by
      have hz : ∀ j, raw10360step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10360step1 = (fun i j => raw10360step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10360step1 raw10360step0; decide +kernel
      have hl : raw10360step1Labels = raw10360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10360step0 raw10360step0Labels permutation56 hz
    mixedMoment B raw10360step1 raw10360step1Labels = mixedMoment B raw10360step2 raw10360step2Labels := by
      have ha : raw10360step2 = (fun i j => raw10360step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10360step2 raw10360step1; decide +kernel
      have hl : raw10360step2Labels = raw10360step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10360step1 raw10360step1Labels permutation10 permutation2
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw10361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10361step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10361 raw10361Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw10361 raw10361Labels = mixedMoment B raw10361step0 raw10361step0Labels := by
      have hz : ∀ j, raw10361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10361step0 = (fun i j => raw10361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10361step0 raw10361; decide +kernel
      have hl : raw10361step0Labels = raw10361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10361 raw10361Labels permutation346 hz
    mixedMoment B raw10361step0 raw10361step0Labels = mixedMoment B raw10361step1 raw10361step1Labels := by
      have hz : ∀ j, raw10361step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10361step1 = (fun i j => raw10361step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10361step1 raw10361step0; decide +kernel
      have hl : raw10361step1Labels = raw10361step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10361step0 raw10361step0Labels permutation56 hz
    mixedMoment B raw10361step1 raw10361step1Labels = mixedMoment B raw10361step2 raw10361step2Labels := by
      have ha : raw10361step2 = (fun i j => raw10361step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10361step2 raw10361step1; decide +kernel
      have hl : raw10361step2Labels = raw10361step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10361step1 raw10361step1Labels permutation9 permutation2
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw10362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10362step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10362step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10362 raw10362Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw10362 raw10362Labels = mixedMoment B raw10362step0 raw10362step0Labels := by
      have hz : ∀ j, raw10362 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10362step0 = (fun i j => raw10362 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10362step0 raw10362; decide +kernel
      have hl : raw10362step0Labels = raw10362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10362 raw10362Labels permutation346 hz
    mixedMoment B raw10362step0 raw10362step0Labels = mixedMoment B raw10362step1 raw10362step1Labels := by
      have hz : ∀ j, raw10362step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10362step1 = (fun i j => raw10362step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10362step1 raw10362step0; decide +kernel
      have hl : raw10362step1Labels = raw10362step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10362step0 raw10362step0Labels permutation56 hz
    mixedMoment B raw10362step1 raw10362step1Labels = mixedMoment B raw10362step2 raw10362step2Labels := by
      have ha : raw10362step2 = (fun i j => raw10362step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10362step2 raw10362step1; decide +kernel
      have hl : raw10362step2Labels = raw10362step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10362step1 raw10362step1Labels permutation9 permutation2
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw10363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10363step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10363 raw10363Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw10363 raw10363Labels = mixedMoment B raw10363step0 raw10363step0Labels := by
      have hz : ∀ j, raw10363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10363step0 = (fun i j => raw10363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10363step0 raw10363; decide +kernel
      have hl : raw10363step0Labels = raw10363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10363 raw10363Labels permutation346 hz
    mixedMoment B raw10363step0 raw10363step0Labels = mixedMoment B raw10363step1 raw10363step1Labels := by
      have ha : raw10363step1 = (fun i j => raw10363step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10363step1 raw10363step0; decide +kernel
      have hl : raw10363step1Labels = raw10363step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10363step0 raw10363step0Labels permutation33 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw10364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10364 raw10364Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw10364 raw10364Labels = mixedMoment B raw10364step0 raw10364step0Labels := by
      have hz : ∀ j, raw10364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10364step0 = (fun i j => raw10364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10364step0 raw10364; decide +kernel
      have hl : raw10364step0Labels = raw10364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10364 raw10364Labels permutation265 hz
    mixedMoment B raw10364step0 raw10364step0Labels = mixedMoment B raw10364step1 raw10364step1Labels := by
      have ha : raw10364step1 = (fun i j => raw10364step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10364step1 raw10364step0; decide +kernel
      have hl : raw10364step1Labels = raw10364step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10364step0 raw10364step0Labels permutation33 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw10365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10365step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10365step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10365 raw10365Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw10365 raw10365Labels = mixedMoment B raw10365step0 raw10365step0Labels := by
      have hz : ∀ j, raw10365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10365step0 = (fun i j => raw10365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10365step0 raw10365; decide +kernel
      have hl : raw10365step0Labels = raw10365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10365 raw10365Labels permutation346 hz
    mixedMoment B raw10365step0 raw10365step0Labels = mixedMoment B raw10365step1 raw10365step1Labels := by
      have hz : ∀ j, raw10365step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10365step1 = (fun i j => raw10365step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10365step1 raw10365step0; decide +kernel
      have hl : raw10365step1Labels = raw10365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10365step0 raw10365step0Labels permutation56 hz
    mixedMoment B raw10365step1 raw10365step1Labels = mixedMoment B raw10365step2 raw10365step2Labels := by
      have ha : raw10365step2 = (fun i j => raw10365step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10365step2 raw10365step1; decide +kernel
      have hl : raw10365step2Labels = raw10365step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10365step1 raw10365step1Labels permutation9 permutation2
    _ = mixedMoment B node5111 node5111Labels := by rfl

def raw10366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10366step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10366step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10366 raw10366Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw10366 raw10366Labels = mixedMoment B raw10366step0 raw10366step0Labels := by
      have hz : ∀ j, raw10366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10366step0 = (fun i j => raw10366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10366step0 raw10366; decide +kernel
      have hl : raw10366step0Labels = raw10366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10366 raw10366Labels permutation346 hz
    mixedMoment B raw10366step0 raw10366step0Labels = mixedMoment B raw10366step1 raw10366step1Labels := by
      have hz : ∀ j, raw10366step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10366step1 = (fun i j => raw10366step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10366step1 raw10366step0; decide +kernel
      have hl : raw10366step1Labels = raw10366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10366step0 raw10366step0Labels permutation56 hz
    mixedMoment B raw10366step1 raw10366step1Labels = mixedMoment B raw10366step2 raw10366step2Labels := by
      have ha : raw10366step2 = (fun i j => raw10366step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10366step2 raw10366step1; decide +kernel
      have hl : raw10366step2Labels = raw10366step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10366step1 raw10366step1Labels permutation9 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw10367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10367 raw10367Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw10367 raw10367Labels = mixedMoment B raw10367step0 raw10367step0Labels := by
      have hz : ∀ j, raw10367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10367step0 = (fun i j => raw10367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10367step0 raw10367; decide +kernel
      have hl : raw10367step0Labels = raw10367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10367 raw10367Labels permutation346 hz
    mixedMoment B raw10367step0 raw10367step0Labels = mixedMoment B raw10367step1 raw10367step1Labels := by
      have hz : ∀ j, raw10367step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10367step1 = (fun i j => raw10367step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10367step1 raw10367step0; decide +kernel
      have hl : raw10367step1Labels = raw10367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10367step0 raw10367step0Labels permutation56 hz
    _ = mixedMoment B node4609 node4609Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
