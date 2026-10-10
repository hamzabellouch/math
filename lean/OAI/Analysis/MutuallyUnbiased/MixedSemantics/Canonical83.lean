import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10624 raw10624Labels = mixedMoment B node3003 node3003Labels := by
  calc
    mixedMoment B raw10624 raw10624Labels = mixedMoment B raw10624step0 raw10624step0Labels := by
      have hz : ∀ j, raw10624 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10624step0 = (fun i j => raw10624 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10624step0 raw10624; decide +kernel
      have hl : raw10624step0Labels = raw10624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10624 raw10624Labels permutation265 hz
    mixedMoment B raw10624step0 raw10624step0Labels = mixedMoment B raw10624step1 raw10624step1Labels := by
      have ha : raw10624step1 = (fun i j => raw10624step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10624step1 raw10624step0; decide +kernel
      have hl : raw10624step1Labels = raw10624step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10624step0 raw10624step0Labels permutation38 permutation3
    _ = mixedMoment B node3003 node3003Labels := by rfl

def raw10625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10625step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10625 raw10625Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw10625 raw10625Labels = mixedMoment B raw10625step0 raw10625step0Labels := by
      have hz : ∀ j, raw10625 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10625step0 = (fun i j => raw10625 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10625step0 raw10625; decide +kernel
      have hl : raw10625step0Labels = raw10625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10625 raw10625Labels permutation520 hz
    mixedMoment B raw10625step0 raw10625step0Labels = mixedMoment B raw10625step1 raw10625step1Labels := by
      have hz : ∀ j, raw10625step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10625step1 = (fun i j => raw10625step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10625step1 raw10625step0; decide +kernel
      have hl : raw10625step1Labels = raw10625step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10625step0 raw10625step0Labels permutation56 hz
    mixedMoment B raw10625step1 raw10625step1Labels = mixedMoment B raw10625step2 raw10625step2Labels := by
      have ha : raw10625step2 = (fun i j => raw10625step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10625step2 raw10625step1; decide +kernel
      have hl : raw10625step2Labels = raw10625step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10625step1 raw10625step1Labels permutation10 permutation3
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw10626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10626 raw10626Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw10626 raw10626Labels = mixedMoment B raw10626step0 raw10626step0Labels := by
      have hz : ∀ j, raw10626 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10626step0 = (fun i j => raw10626 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10626step0 raw10626; decide +kernel
      have hl : raw10626step0Labels = raw10626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10626 raw10626Labels permutation265 hz
    mixedMoment B raw10626step0 raw10626step0Labels = mixedMoment B raw10626step1 raw10626step1Labels := by
      have ha : raw10626step1 = (fun i j => raw10626step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10626step1 raw10626step0; decide +kernel
      have hl : raw10626step1Labels = raw10626step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10626step0 raw10626step0Labels permutation139 permutation6
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw10627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10627step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10627 raw10627Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw10627 raw10627Labels = mixedMoment B raw10627step0 raw10627step0Labels := by
      have hz : ∀ j, raw10627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10627step0 = (fun i j => raw10627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10627step0 raw10627; decide +kernel
      have hl : raw10627step0Labels = raw10627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10627 raw10627Labels permutation346 hz
    mixedMoment B raw10627step0 raw10627step0Labels = mixedMoment B raw10627step1 raw10627step1Labels := by
      have hz : ∀ j, raw10627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10627step1 = (fun i j => raw10627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10627step1 raw10627step0; decide +kernel
      have hl : raw10627step1Labels = raw10627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10627step0 raw10627step0Labels permutation56 hz
    mixedMoment B raw10627step1 raw10627step1Labels = mixedMoment B raw10627step2 raw10627step2Labels := by
      have ha : raw10627step2 = (fun i j => raw10627step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10627step2 raw10627step1; decide +kernel
      have hl : raw10627step2Labels = raw10627step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10627step1 raw10627step1Labels permutation10 permutation3
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw10628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10628step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10628 raw10628Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw10628 raw10628Labels = mixedMoment B raw10628step0 raw10628step0Labels := by
      have hz : ∀ j, raw10628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10628step0 = (fun i j => raw10628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10628step0 raw10628; decide +kernel
      have hl : raw10628step0Labels = raw10628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10628 raw10628Labels permutation346 hz
    mixedMoment B raw10628step0 raw10628step0Labels = mixedMoment B raw10628step1 raw10628step1Labels := by
      have ha : raw10628step1 = (fun i j => raw10628step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10628step1 raw10628step0; decide +kernel
      have hl : raw10628step1Labels = raw10628step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10628step0 raw10628step0Labels permutation34 permutation3
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw10629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10629 raw10629Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw10629 raw10629Labels = mixedMoment B raw10629step0 raw10629step0Labels := by
      have hz : ∀ j, raw10629 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10629step0 = (fun i j => raw10629 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10629step0 raw10629; decide +kernel
      have hl : raw10629step0Labels = raw10629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10629 raw10629Labels permutation265 hz
    mixedMoment B raw10629step0 raw10629step0Labels = mixedMoment B raw10629step1 raw10629step1Labels := by
      have ha : raw10629step1 = (fun i j => raw10629step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10629step1 raw10629step0; decide +kernel
      have hl : raw10629step1Labels = raw10629step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10629step0 raw10629step0Labels permutation34 permutation3
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw10630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10630step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10630step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw10630step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10630step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw10630step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10630 raw10630Labels = mixedMoment B node3125 node3125Labels := by
  calc
    mixedMoment B raw10630 raw10630Labels = mixedMoment B raw10630step0 raw10630step0Labels := by
      have hz : ∀ j, raw10630 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10630step0 = (fun i j => raw10630 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10630step0 raw10630; decide +kernel
      have hl : raw10630step0Labels = raw10630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10630 raw10630Labels permutation520 hz
    mixedMoment B raw10630step0 raw10630step0Labels = mixedMoment B raw10630step1 raw10630step1Labels := by
      have hz : ∀ j, raw10630step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10630step1 = (fun i j => raw10630step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10630step1 raw10630step0; decide +kernel
      have hl : raw10630step1Labels = raw10630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10630step0 raw10630step0Labels permutation80 hz
    mixedMoment B raw10630step1 raw10630step1Labels = mixedMoment B raw10630step2 raw10630step2Labels := by
      have hz : ∀ j, raw10630step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10630step2 = (fun i j => raw10630step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10630step2 raw10630step1; decide +kernel
      have hl : raw10630step2Labels = raw10630step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10630step1 raw10630step1Labels permutation14 hz
    mixedMoment B raw10630step2 raw10630step2Labels = mixedMoment B raw10630step3 raw10630step3Labels := by
      have ha : raw10630step3 = (fun i j => raw10630step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10630step3 raw10630step2; decide +kernel
      have hl : raw10630step3Labels = raw10630step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10630step2 raw10630step2Labels permutation2 permutation3
    _ = mixedMoment B node3125 node3125Labels := by rfl

def raw10631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10631step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10631 raw10631Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw10631 raw10631Labels = mixedMoment B raw10631step0 raw10631step0Labels := by
      have hz : ∀ j, raw10631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10631step0 = (fun i j => raw10631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10631step0 raw10631; decide +kernel
      have hl : raw10631step0Labels = raw10631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10631 raw10631Labels permutation346 hz
    mixedMoment B raw10631step0 raw10631step0Labels = mixedMoment B raw10631step1 raw10631step1Labels := by
      have hz : ∀ j, raw10631step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10631step1 = (fun i j => raw10631step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10631step1 raw10631step0; decide +kernel
      have hl : raw10631step1Labels = raw10631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10631step0 raw10631step0Labels permutation56 hz
    mixedMoment B raw10631step1 raw10631step1Labels = mixedMoment B raw10631step2 raw10631step2Labels := by
      have ha : raw10631step2 = (fun i j => raw10631step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10631step2 raw10631step1; decide +kernel
      have hl : raw10631step2Labels = raw10631step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10631step1 raw10631step1Labels permutation31 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw10632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10632 raw10632Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw10632 raw10632Labels = mixedMoment B raw10632step0 raw10632step0Labels := by
      have hz : ∀ j, raw10632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10632step0 = (fun i j => raw10632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10632step0 raw10632; decide +kernel
      have hl : raw10632step0Labels = raw10632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10632 raw10632Labels permutation346 hz
    mixedMoment B raw10632step0 raw10632step0Labels = mixedMoment B raw10632step1 raw10632step1Labels := by
      have hz : ∀ j, raw10632step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10632step1 = (fun i j => raw10632step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10632step1 raw10632step0; decide +kernel
      have hl : raw10632step1Labels = raw10632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10632step0 raw10632step0Labels permutation56 hz
    mixedMoment B raw10632step1 raw10632step1Labels = mixedMoment B raw10632step2 raw10632step2Labels := by
      have ha : raw10632step2 = (fun i j => raw10632step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10632step2 raw10632step1; decide +kernel
      have hl : raw10632step2Labels = raw10632step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10632step1 raw10632step1Labels permutation9 permutation3
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw10633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10633 raw10633Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw10633 raw10633Labels = mixedMoment B raw10633step0 raw10633step0Labels := by
      have hz : ∀ j, raw10633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10633step0 = (fun i j => raw10633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10633step0 raw10633; decide +kernel
      have hl : raw10633step0Labels = raw10633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10633 raw10633Labels permutation346 hz
    mixedMoment B raw10633step0 raw10633step0Labels = mixedMoment B raw10633step1 raw10633step1Labels := by
      have ha : raw10633step1 = (fun i j => raw10633step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10633step1 raw10633step0; decide +kernel
      have hl : raw10633step1Labels = raw10633step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10633step0 raw10633step0Labels permutation33 permutation3
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw10634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10634 raw10634Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw10634 raw10634Labels = mixedMoment B raw10634step0 raw10634step0Labels := by
      have hz : ∀ j, raw10634 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10634step0 = (fun i j => raw10634 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10634step0 raw10634; decide +kernel
      have hl : raw10634step0Labels = raw10634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10634 raw10634Labels permutation265 hz
    mixedMoment B raw10634step0 raw10634step0Labels = mixedMoment B raw10634step1 raw10634step1Labels := by
      have ha : raw10634step1 = (fun i j => raw10634step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10634step1 raw10634step0; decide +kernel
      have hl : raw10634step1Labels = raw10634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10634step0 raw10634step0Labels permutation33 permutation3
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw10635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw10635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10635 raw10635Labels = mixedMoment B node3005 node3005Labels := by
  calc
    mixedMoment B raw10635 raw10635Labels = mixedMoment B raw10635step0 raw10635step0Labels := by
      have hz : ∀ j, raw10635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10635step0 = (fun i j => raw10635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10635step0 raw10635; decide +kernel
      have hl : raw10635step0Labels = raw10635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10635 raw10635Labels permutation346 hz
    mixedMoment B raw10635step0 raw10635step0Labels = mixedMoment B raw10635step1 raw10635step1Labels := by
      have hz : ∀ j, raw10635step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10635step1 = (fun i j => raw10635step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10635step1 raw10635step0; decide +kernel
      have hl : raw10635step1Labels = raw10635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10635step0 raw10635step0Labels permutation56 hz
    mixedMoment B raw10635step1 raw10635step1Labels = mixedMoment B raw10635step2 raw10635step2Labels := by
      have ha : raw10635step2 = (fun i j => raw10635step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10635step2 raw10635step1; decide +kernel
      have hl : raw10635step2Labels = raw10635step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10635step1 raw10635step1Labels permutation9 permutation3
    _ = mixedMoment B node3005 node3005Labels := by rfl

def raw10636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10636step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10636 raw10636Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw10636 raw10636Labels = mixedMoment B raw10636step0 raw10636step0Labels := by
      have hz : ∀ j, raw10636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10636step0 = (fun i j => raw10636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10636step0 raw10636; decide +kernel
      have hl : raw10636step0Labels = raw10636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10636 raw10636Labels permutation346 hz
    mixedMoment B raw10636step0 raw10636step0Labels = mixedMoment B raw10636step1 raw10636step1Labels := by
      have hz : ∀ j, raw10636step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10636step1 = (fun i j => raw10636step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10636step1 raw10636step0; decide +kernel
      have hl : raw10636step1Labels = raw10636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10636step0 raw10636step0Labels permutation56 hz
    mixedMoment B raw10636step1 raw10636step1Labels = mixedMoment B raw10636step2 raw10636step2Labels := by
      have ha : raw10636step2 = (fun i j => raw10636step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10636step2 raw10636step1; decide +kernel
      have hl : raw10636step2Labels = raw10636step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10636step1 raw10636step1Labels permutation31 permutation6
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw10637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10637 raw10637Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw10637 raw10637Labels = mixedMoment B raw10637step0 raw10637step0Labels := by
      have hz : ∀ j, raw10637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10637step0 = (fun i j => raw10637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10637step0 raw10637; decide +kernel
      have hl : raw10637step0Labels = raw10637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10637 raw10637Labels permutation346 hz
    mixedMoment B raw10637step0 raw10637step0Labels = mixedMoment B raw10637step1 raw10637step1Labels := by
      have hz : ∀ j, raw10637step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10637step1 = (fun i j => raw10637step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10637step1 raw10637step0; decide +kernel
      have hl : raw10637step1Labels = raw10637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10637step0 raw10637step0Labels permutation56 hz
    mixedMoment B raw10637step1 raw10637step1Labels = mixedMoment B raw10637step2 raw10637step2Labels := by
      have ha : raw10637step2 = (fun i j => raw10637step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10637step2 raw10637step1; decide +kernel
      have hl : raw10637step2Labels = raw10637step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10637step1 raw10637step1Labels permutation8 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw10638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10638 raw10638Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw10638 raw10638Labels = mixedMoment B raw10638step0 raw10638step0Labels := by
      have hz : ∀ j, raw10638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10638step0 = (fun i j => raw10638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10638step0 raw10638; decide +kernel
      have hl : raw10638step0Labels = raw10638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10638 raw10638Labels permutation346 hz
    mixedMoment B raw10638step0 raw10638step0Labels = mixedMoment B raw10638step1 raw10638step1Labels := by
      have ha : raw10638step1 = (fun i j => raw10638step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10638step1 raw10638step0; decide +kernel
      have hl : raw10638step1Labels = raw10638step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10638step0 raw10638step0Labels permutation32 permutation3
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw10639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10639 raw10639Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw10639 raw10639Labels = mixedMoment B raw10639step0 raw10639step0Labels := by
      have hz : ∀ j, raw10639 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10639step0 = (fun i j => raw10639 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10639step0 raw10639; decide +kernel
      have hl : raw10639step0Labels = raw10639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10639 raw10639Labels permutation265 hz
    mixedMoment B raw10639step0 raw10639step0Labels = mixedMoment B raw10639step1 raw10639step1Labels := by
      have ha : raw10639step1 = (fun i j => raw10639step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10639step1 raw10639step0; decide +kernel
      have hl : raw10639step1Labels = raw10639step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10639step0 raw10639step0Labels permutation32 permutation3
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw10640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10640 raw10640Labels = mixedMoment B node3004 node3004Labels := by
  calc
    mixedMoment B raw10640 raw10640Labels = mixedMoment B raw10640step0 raw10640step0Labels := by
      have hz : ∀ j, raw10640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10640step0 = (fun i j => raw10640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10640step0 raw10640; decide +kernel
      have hl : raw10640step0Labels = raw10640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10640 raw10640Labels permutation346 hz
    mixedMoment B raw10640step0 raw10640step0Labels = mixedMoment B raw10640step1 raw10640step1Labels := by
      have hz : ∀ j, raw10640step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10640step1 = (fun i j => raw10640step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10640step1 raw10640step0; decide +kernel
      have hl : raw10640step1Labels = raw10640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10640step0 raw10640step0Labels permutation56 hz
    mixedMoment B raw10640step1 raw10640step1Labels = mixedMoment B raw10640step2 raw10640step2Labels := by
      have ha : raw10640step2 = (fun i j => raw10640step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10640step2 raw10640step1; decide +kernel
      have hl : raw10640step2Labels = raw10640step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10640step1 raw10640step1Labels permutation8 permutation3
    _ = mixedMoment B node3004 node3004Labels := by rfl

def raw10641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw10641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10641step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10641step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10641step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw10641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10641 raw10641Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw10641 raw10641Labels = mixedMoment B raw10641step0 raw10641step0Labels := by
      have hz : ∀ j, raw10641 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10641step0 = (fun i j => raw10641 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10641step0 raw10641; decide +kernel
      have hl : raw10641step0Labels = raw10641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10641 raw10641Labels permutation520 hz
    mixedMoment B raw10641step0 raw10641step0Labels = mixedMoment B raw10641step1 raw10641step1Labels := by
      have hz : ∀ j, raw10641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10641step1 = (fun i j => raw10641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10641step1 raw10641step0; decide +kernel
      have hl : raw10641step1Labels = raw10641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10641step0 raw10641step0Labels permutation80 hz
    mixedMoment B raw10641step1 raw10641step1Labels = mixedMoment B raw10641step2 raw10641step2Labels := by
      have hz : ∀ j, raw10641step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10641step2 = (fun i j => raw10641step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10641step2 raw10641step1; decide +kernel
      have hl : raw10641step2Labels = raw10641step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10641step1 raw10641step1Labels permutation14 hz
    mixedMoment B raw10641step2 raw10641step2Labels = mixedMoment B raw10641step3 raw10641step3Labels := by
      have ha : raw10641step3 = (fun i j => raw10641step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10641step3 raw10641step2; decide +kernel
      have hl : raw10641step3Labels = raw10641step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10641step2 raw10641step2Labels permutation2 permutation3
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw10642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10642 raw10642Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10642 raw10642Labels = mixedMoment B raw10642step0 raw10642step0Labels := by
      have hz : ∀ j, raw10642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10642step0 = (fun i j => raw10642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10642step0 raw10642; decide +kernel
      have hl : raw10642step0Labels = raw10642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10642 raw10642Labels permutation346 hz
    mixedMoment B raw10642step0 raw10642step0Labels = mixedMoment B raw10642step1 raw10642step1Labels := by
      have ha : raw10642step1 = (fun i j => raw10642step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10642step1 raw10642step0; decide +kernel
      have hl : raw10642step1Labels = raw10642step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10642step0 raw10642step0Labels permutation149 permutation7
    mixedMoment B raw10642step1 raw10642step1Labels = mixedMoment B raw10642step2 raw10642step2Labels := by
      have ha : raw10642step2 = raw10642step1 := by apply Matrix.ext; unfold raw10642step2 raw10642step1; decide +kernel
      have hl : raw10642step1Labels = labelEmbedding1 ∘ raw10642step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10642step1 raw10642step1Labels raw10642step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw10643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10643step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10643 raw10643Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10643 raw10643Labels = mixedMoment B raw10643step0 raw10643step0Labels := by
      have hz : ∀ j, raw10643 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10643step0 = (fun i j => raw10643 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10643step0 raw10643; decide +kernel
      have hl : raw10643step0Labels = raw10643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10643 raw10643Labels permutation265 hz
    mixedMoment B raw10643step0 raw10643step0Labels = mixedMoment B raw10643step1 raw10643step1Labels := by
      have ha : raw10643step1 = (fun i j => raw10643step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10643step1 raw10643step0; decide +kernel
      have hl : raw10643step1Labels = raw10643step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10643step0 raw10643step0Labels permutation149 permutation7
    mixedMoment B raw10643step1 raw10643step1Labels = mixedMoment B raw10643step2 raw10643step2Labels := by
      have ha : raw10643step2 = raw10643step1 := by apply Matrix.ext; unfold raw10643step2 raw10643step1; decide +kernel
      have hl : raw10643step1Labels = labelEmbedding1 ∘ raw10643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10643step1 raw10643step1Labels raw10643step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw10644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10644step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10644step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10644step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10644step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10644step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10644 raw10644Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw10644 raw10644Labels = mixedMoment B raw10644step0 raw10644step0Labels := by
      have hz : ∀ j, raw10644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10644step0 = (fun i j => raw10644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10644step0 raw10644; decide +kernel
      have hl : raw10644step0Labels = raw10644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10644 raw10644Labels permutation346 hz
    mixedMoment B raw10644step0 raw10644step0Labels = mixedMoment B raw10644step1 raw10644step1Labels := by
      have hz : ∀ j, raw10644step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10644step1 = (fun i j => raw10644step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10644step1 raw10644step0; decide +kernel
      have hl : raw10644step1Labels = raw10644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10644step0 raw10644step0Labels permutation56 hz
    mixedMoment B raw10644step1 raw10644step1Labels = mixedMoment B raw10644step2 raw10644step2Labels := by
      have ha : raw10644step2 = (fun i j => raw10644step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10644step2 raw10644step1; decide +kernel
      have hl : raw10644step2Labels = raw10644step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10644step1 raw10644step1Labels permutation31 permutation7
    mixedMoment B raw10644step2 raw10644step2Labels = mixedMoment B raw10644step3 raw10644step3Labels := by
      have ha : raw10644step3 = raw10644step2 := by apply Matrix.ext; unfold raw10644step3 raw10644step2; decide +kernel
      have hl : raw10644step2Labels = labelEmbedding1 ∘ raw10644step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10644step2 raw10644step2Labels raw10644step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw10645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10645step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10645step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10645step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw10645step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10645step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10645step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10645step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10645step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10645 raw10645Labels = mixedMoment B node2786 node2786Labels := by
  calc
    mixedMoment B raw10645 raw10645Labels = mixedMoment B raw10645step0 raw10645step0Labels := by
      have hz : ∀ j, raw10645 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10645step0 = (fun i j => raw10645 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10645step0 raw10645; decide +kernel
      have hl : raw10645step0Labels = raw10645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10645 raw10645Labels permutation520 hz
    mixedMoment B raw10645step0 raw10645step0Labels = mixedMoment B raw10645step1 raw10645step1Labels := by
      have hz : ∀ j, raw10645step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10645step1 = (fun i j => raw10645step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10645step1 raw10645step0; decide +kernel
      have hl : raw10645step1Labels = raw10645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10645step0 raw10645step0Labels permutation80 hz
    mixedMoment B raw10645step1 raw10645step1Labels = mixedMoment B raw10645step2 raw10645step2Labels := by
      have hz : ∀ j, raw10645step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10645step2 = (fun i j => raw10645step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10645step2 raw10645step1; decide +kernel
      have hl : raw10645step2Labels = raw10645step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10645step1 raw10645step1Labels permutation14 hz
    mixedMoment B raw10645step2 raw10645step2Labels = mixedMoment B raw10645step3 raw10645step3Labels := by
      have ha : raw10645step3 = (fun i j => raw10645step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10645step3 raw10645step2; decide +kernel
      have hl : raw10645step3Labels = raw10645step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10645step2 raw10645step2Labels permutation7 permutation7
    mixedMoment B raw10645step3 raw10645step3Labels = mixedMoment B raw10645step4 raw10645step4Labels := by
      have ha : raw10645step4 = raw10645step3 := by apply Matrix.ext; unfold raw10645step4 raw10645step3; decide +kernel
      have hl : raw10645step3Labels = labelEmbedding1 ∘ raw10645step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10645step3 raw10645step3Labels raw10645step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2786 node2786Labels := by rfl

def raw10646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10646step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10646step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10646step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10646 raw10646Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw10646 raw10646Labels = mixedMoment B raw10646step0 raw10646step0Labels := by
      have hz : ∀ j, raw10646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10646step0 = (fun i j => raw10646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10646step0 raw10646; decide +kernel
      have hl : raw10646step0Labels = raw10646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10646 raw10646Labels permutation346 hz
    mixedMoment B raw10646step0 raw10646step0Labels = mixedMoment B raw10646step1 raw10646step1Labels := by
      have hz : ∀ j, raw10646step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10646step1 = (fun i j => raw10646step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10646step1 raw10646step0; decide +kernel
      have hl : raw10646step1Labels = raw10646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10646step0 raw10646step0Labels permutation56 hz
    mixedMoment B raw10646step1 raw10646step1Labels = mixedMoment B raw10646step2 raw10646step2Labels := by
      have ha : raw10646step2 = (fun i j => raw10646step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10646step2 raw10646step1; decide +kernel
      have hl : raw10646step2Labels = raw10646step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10646step1 raw10646step1Labels permutation31 permutation7
    mixedMoment B raw10646step2 raw10646step2Labels = mixedMoment B raw10646step3 raw10646step3Labels := by
      have ha : raw10646step3 = raw10646step2 := by apply Matrix.ext; unfold raw10646step3 raw10646step2; decide +kernel
      have hl : raw10646step2Labels = labelEmbedding1 ∘ raw10646step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10646step2 raw10646step2Labels raw10646step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw10647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10647step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10647 raw10647Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw10647 raw10647Labels = mixedMoment B raw10647step0 raw10647step0Labels := by
      have hz : ∀ j, raw10647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10647step0 = (fun i j => raw10647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10647step0 raw10647; decide +kernel
      have hl : raw10647step0Labels = raw10647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10647 raw10647Labels permutation346 hz
    mixedMoment B raw10647step0 raw10647step0Labels = mixedMoment B raw10647step1 raw10647step1Labels := by
      have ha : raw10647step1 = (fun i j => raw10647step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10647step1 raw10647step0; decide +kernel
      have hl : raw10647step1Labels = raw10647step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10647step0 raw10647step0Labels permutation139 permutation7
    mixedMoment B raw10647step1 raw10647step1Labels = mixedMoment B raw10647step2 raw10647step2Labels := by
      have ha : raw10647step2 = raw10647step1 := by apply Matrix.ext; unfold raw10647step2 raw10647step1; decide +kernel
      have hl : raw10647step1Labels = labelEmbedding1 ∘ raw10647step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10647step1 raw10647step1Labels raw10647step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw10648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10648 raw10648Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw10648 raw10648Labels = mixedMoment B raw10648step0 raw10648step0Labels := by
      have ha : raw10648step0 = (fun i j => raw10648 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10648step0 raw10648; decide +kernel
      have hl : raw10648step0Labels = raw10648Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10648 raw10648Labels permutation620 permutation7
    mixedMoment B raw10648step0 raw10648step0Labels = mixedMoment B raw10648step1 raw10648step1Labels := by
      have ha : raw10648step1 = raw10648step0 := by apply Matrix.ext; unfold raw10648step1 raw10648step0; decide +kernel
      have hl : raw10648step0Labels = labelEmbedding1 ∘ raw10648step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10648step0 raw10648step0Labels raw10648step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2693 node2693Labels := by rfl

def raw10649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10649step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10649 raw10649Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw10649 raw10649Labels = mixedMoment B raw10649step0 raw10649step0Labels := by
      have hz : ∀ j, raw10649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10649step0 = (fun i j => raw10649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10649step0 raw10649; decide +kernel
      have hl : raw10649step0Labels = raw10649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10649 raw10649Labels permutation346 hz
    mixedMoment B raw10649step0 raw10649step0Labels = mixedMoment B raw10649step1 raw10649step1Labels := by
      have ha : raw10649step1 = (fun i j => raw10649step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10649step1 raw10649step0; decide +kernel
      have hl : raw10649step1Labels = raw10649step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10649step0 raw10649step0Labels permutation139 permutation7
    mixedMoment B raw10649step1 raw10649step1Labels = mixedMoment B raw10649step2 raw10649step2Labels := by
      have ha : raw10649step2 = raw10649step1 := by apply Matrix.ext; unfold raw10649step2 raw10649step1; decide +kernel
      have hl : raw10649step1Labels = labelEmbedding1 ∘ raw10649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10649step1 raw10649step1Labels raw10649step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw10650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10650Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10650step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10650step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10650step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10650step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10650 raw10650Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw10650 raw10650Labels = mixedMoment B raw10650step0 raw10650step0Labels := by
      have hz : ∀ j, raw10650 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10650step0 = (fun i j => raw10650 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10650step0 raw10650; decide +kernel
      have hl : raw10650step0Labels = raw10650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10650 raw10650Labels permutation520 hz
    mixedMoment B raw10650step0 raw10650step0Labels = mixedMoment B raw10650step1 raw10650step1Labels := by
      have hz : ∀ j, raw10650step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10650step1 = (fun i j => raw10650step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10650step1 raw10650step0; decide +kernel
      have hl : raw10650step1Labels = raw10650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10650step0 raw10650step0Labels permutation80 hz
    mixedMoment B raw10650step1 raw10650step1Labels = mixedMoment B raw10650step2 raw10650step2Labels := by
      have ha : raw10650step2 = (fun i j => raw10650step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10650step2 raw10650step1; decide +kernel
      have hl : raw10650step2Labels = raw10650step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10650step1 raw10650step1Labels permutation29 permutation7
    mixedMoment B raw10650step2 raw10650step2Labels = mixedMoment B raw10650step3 raw10650step3Labels := by
      have ha : raw10650step3 = raw10650step2 := by apply Matrix.ext; unfold raw10650step3 raw10650step2; decide +kernel
      have hl : raw10650step2Labels = labelEmbedding1 ∘ raw10650step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10650step2 raw10650step2Labels raw10650step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw10651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10651Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10651step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10651step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10651 raw10651Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw10651 raw10651Labels = mixedMoment B raw10651step0 raw10651step0Labels := by
      have hz : ∀ j, raw10651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10651step0 = (fun i j => raw10651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10651step0 raw10651; decide +kernel
      have hl : raw10651step0Labels = raw10651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10651 raw10651Labels permutation346 hz
    mixedMoment B raw10651step0 raw10651step0Labels = mixedMoment B raw10651step1 raw10651step1Labels := by
      have ha : raw10651step1 = (fun i j => raw10651step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10651step1 raw10651step0; decide +kernel
      have hl : raw10651step1Labels = raw10651step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10651step0 raw10651step0Labels permutation139 permutation7
    mixedMoment B raw10651step1 raw10651step1Labels = mixedMoment B raw10651step2 raw10651step2Labels := by
      have ha : raw10651step2 = raw10651step1 := by apply Matrix.ext; unfold raw10651step2 raw10651step1; decide +kernel
      have hl : raw10651step1Labels = labelEmbedding1 ∘ raw10651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10651step1 raw10651step1Labels raw10651step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw10652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10652Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10652step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10652step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10652 raw10652Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw10652 raw10652Labels = mixedMoment B raw10652step0 raw10652step0Labels := by
      have hz : ∀ j, raw10652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10652step0 = (fun i j => raw10652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10652step0 raw10652; decide +kernel
      have hl : raw10652step0Labels = raw10652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10652 raw10652Labels permutation265 hz
    mixedMoment B raw10652step0 raw10652step0Labels = mixedMoment B raw10652step1 raw10652step1Labels := by
      have ha : raw10652step1 = (fun i j => raw10652step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10652step1 raw10652step0; decide +kernel
      have hl : raw10652step1Labels = raw10652step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10652step0 raw10652step0Labels permutation139 permutation7
    mixedMoment B raw10652step1 raw10652step1Labels = mixedMoment B raw10652step2 raw10652step2Labels := by
      have ha : raw10652step2 = raw10652step1 := by apply Matrix.ext; unfold raw10652step2 raw10652step1; decide +kernel
      have hl : raw10652step1Labels = labelEmbedding1 ∘ raw10652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10652step1 raw10652step1Labels raw10652step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw10653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10653Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10653step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10653 raw10653Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw10653 raw10653Labels = mixedMoment B raw10653step0 raw10653step0Labels := by
      have ha : raw10653step0 = (fun i j => raw10653 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10653step0 raw10653; decide +kernel
      have hl : raw10653step0Labels = raw10653Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10653 raw10653Labels permutation644 permutation7
    mixedMoment B raw10653step0 raw10653step0Labels = mixedMoment B raw10653step1 raw10653step1Labels := by
      have ha : raw10653step1 = raw10653step0 := by apply Matrix.ext; unfold raw10653step1 raw10653step0; decide +kernel
      have hl : raw10653step0Labels = labelEmbedding1 ∘ raw10653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10653step0 raw10653step0Labels raw10653step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2693 node2693Labels := by rfl

def raw10654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10654Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10654step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10654step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10654 raw10654Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw10654 raw10654Labels = mixedMoment B raw10654step0 raw10654step0Labels := by
      have hz : ∀ j, raw10654 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10654step0 = (fun i j => raw10654 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10654step0 raw10654; decide +kernel
      have hl : raw10654step0Labels = raw10654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10654 raw10654Labels permutation265 hz
    mixedMoment B raw10654step0 raw10654step0Labels = mixedMoment B raw10654step1 raw10654step1Labels := by
      have ha : raw10654step1 = (fun i j => raw10654step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10654step1 raw10654step0; decide +kernel
      have hl : raw10654step1Labels = raw10654step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10654step0 raw10654step0Labels permutation139 permutation7
    mixedMoment B raw10654step1 raw10654step1Labels = mixedMoment B raw10654step2 raw10654step2Labels := by
      have ha : raw10654step2 = raw10654step1 := by apply Matrix.ext; unfold raw10654step2 raw10654step1; decide +kernel
      have hl : raw10654step1Labels = labelEmbedding1 ∘ raw10654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10654step1 raw10654step1Labels raw10654step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw10655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10655Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10655step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10655step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10655step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10655step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10655step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10655 raw10655Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw10655 raw10655Labels = mixedMoment B raw10655step0 raw10655step0Labels := by
      have hz : ∀ j, raw10655 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10655step0 = (fun i j => raw10655 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10655step0 raw10655; decide +kernel
      have hl : raw10655step0Labels = raw10655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10655 raw10655Labels permutation520 hz
    mixedMoment B raw10655step0 raw10655step0Labels = mixedMoment B raw10655step1 raw10655step1Labels := by
      have hz : ∀ j, raw10655step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10655step1 = (fun i j => raw10655step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10655step1 raw10655step0; decide +kernel
      have hl : raw10655step1Labels = raw10655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10655step0 raw10655step0Labels permutation56 hz
    mixedMoment B raw10655step1 raw10655step1Labels = mixedMoment B raw10655step2 raw10655step2Labels := by
      have ha : raw10655step2 = (fun i j => raw10655step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10655step2 raw10655step1; decide +kernel
      have hl : raw10655step2Labels = raw10655step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10655step1 raw10655step1Labels permutation29 permutation7
    mixedMoment B raw10655step2 raw10655step2Labels = mixedMoment B raw10655step3 raw10655step3Labels := by
      have ha : raw10655step3 = raw10655step2 := by apply Matrix.ext; unfold raw10655step3 raw10655step2; decide +kernel
      have hl : raw10655step2Labels = labelEmbedding1 ∘ raw10655step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10655step2 raw10655step2Labels raw10655step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw10656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10656step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10656step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10656 raw10656Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw10656 raw10656Labels = mixedMoment B raw10656step0 raw10656step0Labels := by
      have hz : ∀ j, raw10656 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10656step0 = (fun i j => raw10656 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10656step0 raw10656; decide +kernel
      have hl : raw10656step0Labels = raw10656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10656 raw10656Labels permutation265 hz
    mixedMoment B raw10656step0 raw10656step0Labels = mixedMoment B raw10656step1 raw10656step1Labels := by
      have ha : raw10656step1 = (fun i j => raw10656step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10656step1 raw10656step0; decide +kernel
      have hl : raw10656step1Labels = raw10656step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10656step0 raw10656step0Labels permutation139 permutation7
    mixedMoment B raw10656step1 raw10656step1Labels = mixedMoment B raw10656step2 raw10656step2Labels := by
      have ha : raw10656step2 = raw10656step1 := by apply Matrix.ext; unfold raw10656step2 raw10656step1; decide +kernel
      have hl : raw10656step1Labels = labelEmbedding1 ∘ raw10656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10656step1 raw10656step1Labels raw10656step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw10657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10657Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10657step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10657step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10657step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10657step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10657 raw10657Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10657 raw10657Labels = mixedMoment B raw10657step0 raw10657step0Labels := by
      have hz : ∀ j, raw10657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10657step0 = (fun i j => raw10657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10657step0 raw10657; decide +kernel
      have hl : raw10657step0Labels = raw10657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10657 raw10657Labels permutation346 hz
    mixedMoment B raw10657step0 raw10657step0Labels = mixedMoment B raw10657step1 raw10657step1Labels := by
      have hz : ∀ j, raw10657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10657step1 = (fun i j => raw10657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10657step1 raw10657step0; decide +kernel
      have hl : raw10657step1Labels = raw10657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10657step0 raw10657step0Labels permutation56 hz
    mixedMoment B raw10657step1 raw10657step1Labels = mixedMoment B raw10657step2 raw10657step2Labels := by
      have ha : raw10657step2 = (fun i j => raw10657step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10657step2 raw10657step1; decide +kernel
      have hl : raw10657step2Labels = raw10657step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10657step1 raw10657step1Labels permutation31 permutation7
    mixedMoment B raw10657step2 raw10657step2Labels = mixedMoment B raw10657step3 raw10657step3Labels := by
      have ha : raw10657step3 = raw10657step2 := by apply Matrix.ext; unfold raw10657step3 raw10657step2; decide +kernel
      have hl : raw10657step2Labels = labelEmbedding1 ∘ raw10657step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10657step2 raw10657step2Labels raw10657step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw10658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10658step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10658 raw10658Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10658 raw10658Labels = mixedMoment B raw10658step0 raw10658step0Labels := by
      have hz : ∀ j, raw10658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10658step0 = (fun i j => raw10658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10658step0 raw10658; decide +kernel
      have hl : raw10658step0Labels = raw10658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10658 raw10658Labels permutation346 hz
    mixedMoment B raw10658step0 raw10658step0Labels = mixedMoment B raw10658step1 raw10658step1Labels := by
      have ha : raw10658step1 = (fun i j => raw10658step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10658step1 raw10658step0; decide +kernel
      have hl : raw10658step1Labels = raw10658step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10658step0 raw10658step0Labels permutation149 permutation7
    mixedMoment B raw10658step1 raw10658step1Labels = mixedMoment B raw10658step2 raw10658step2Labels := by
      have ha : raw10658step2 = raw10658step1 := by apply Matrix.ext; unfold raw10658step2 raw10658step1; decide +kernel
      have hl : raw10658step1Labels = labelEmbedding1 ∘ raw10658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10658step1 raw10658step1Labels raw10658step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw10659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10659Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10659step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10659step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10659step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10659 raw10659Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw10659 raw10659Labels = mixedMoment B raw10659step0 raw10659step0Labels := by
      have hz : ∀ j, raw10659 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10659step0 = (fun i j => raw10659 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10659step0 raw10659; decide +kernel
      have hl : raw10659step0Labels = raw10659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10659 raw10659Labels permutation265 hz
    mixedMoment B raw10659step0 raw10659step0Labels = mixedMoment B raw10659step1 raw10659step1Labels := by
      have ha : raw10659step1 = (fun i j => raw10659step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10659step1 raw10659step0; decide +kernel
      have hl : raw10659step1Labels = raw10659step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10659step0 raw10659step0Labels permutation149 permutation7
    mixedMoment B raw10659step1 raw10659step1Labels = mixedMoment B raw10659step2 raw10659step2Labels := by
      have ha : raw10659step2 = raw10659step1 := by apply Matrix.ext; unfold raw10659step2 raw10659step1; decide +kernel
      have hl : raw10659step1Labels = labelEmbedding1 ∘ raw10659step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10659step1 raw10659step1Labels raw10659step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw10660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10660Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10660step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10660step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10660step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw10660step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10660step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw10660step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10660step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw10660step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10660 raw10660Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw10660 raw10660Labels = mixedMoment B raw10660step0 raw10660step0Labels := by
      have hz : ∀ j, raw10660 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10660step0 = (fun i j => raw10660 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10660step0 raw10660; decide +kernel
      have hl : raw10660step0Labels = raw10660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10660 raw10660Labels permutation520 hz
    mixedMoment B raw10660step0 raw10660step0Labels = mixedMoment B raw10660step1 raw10660step1Labels := by
      have hz : ∀ j, raw10660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10660step1 = (fun i j => raw10660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10660step1 raw10660step0; decide +kernel
      have hl : raw10660step1Labels = raw10660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10660step0 raw10660step0Labels permutation80 hz
    mixedMoment B raw10660step1 raw10660step1Labels = mixedMoment B raw10660step2 raw10660step2Labels := by
      have hz : ∀ j, raw10660step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10660step2 = (fun i j => raw10660step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10660step2 raw10660step1; decide +kernel
      have hl : raw10660step2Labels = raw10660step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10660step1 raw10660step1Labels permutation14 hz
    mixedMoment B raw10660step2 raw10660step2Labels = mixedMoment B raw10660step3 raw10660step3Labels := by
      have ha : raw10660step3 = (fun i j => raw10660step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10660step3 raw10660step2; decide +kernel
      have hl : raw10660step3Labels = raw10660step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10660step2 raw10660step2Labels permutation7 permutation7
    mixedMoment B raw10660step3 raw10660step3Labels = mixedMoment B raw10660step4 raw10660step4Labels := by
      have ha : raw10660step4 = raw10660step3 := by apply Matrix.ext; unfold raw10660step4 raw10660step3; decide +kernel
      have hl : raw10660step3Labels = labelEmbedding1 ∘ raw10660step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10660step3 raw10660step3Labels raw10660step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw10661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10661Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10661step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10661step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10661step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10661step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10661 raw10661Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw10661 raw10661Labels = mixedMoment B raw10661step0 raw10661step0Labels := by
      have hz : ∀ j, raw10661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10661step0 = (fun i j => raw10661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10661step0 raw10661; decide +kernel
      have hl : raw10661step0Labels = raw10661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10661 raw10661Labels permutation346 hz
    mixedMoment B raw10661step0 raw10661step0Labels = mixedMoment B raw10661step1 raw10661step1Labels := by
      have hz : ∀ j, raw10661step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10661step1 = (fun i j => raw10661step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10661step1 raw10661step0; decide +kernel
      have hl : raw10661step1Labels = raw10661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10661step0 raw10661step0Labels permutation56 hz
    mixedMoment B raw10661step1 raw10661step1Labels = mixedMoment B raw10661step2 raw10661step2Labels := by
      have ha : raw10661step2 = (fun i j => raw10661step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10661step2 raw10661step1; decide +kernel
      have hl : raw10661step2Labels = raw10661step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10661step1 raw10661step1Labels permutation31 permutation7
    mixedMoment B raw10661step2 raw10661step2Labels = mixedMoment B raw10661step3 raw10661step3Labels := by
      have ha : raw10661step3 = raw10661step2 := by apply Matrix.ext; unfold raw10661step3 raw10661step2; decide +kernel
      have hl : raw10661step2Labels = labelEmbedding1 ∘ raw10661step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10661step2 raw10661step2Labels raw10661step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw10662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10662Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10662step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10662step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw10662step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw10662step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10662 raw10662Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw10662 raw10662Labels = mixedMoment B raw10662step0 raw10662step0Labels := by
      have hz : ∀ j, raw10662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10662step0 = (fun i j => raw10662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10662step0 raw10662; decide +kernel
      have hl : raw10662step0Labels = raw10662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10662 raw10662Labels permutation346 hz
    mixedMoment B raw10662step0 raw10662step0Labels = mixedMoment B raw10662step1 raw10662step1Labels := by
      have hz : ∀ j, raw10662step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10662step1 = (fun i j => raw10662step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10662step1 raw10662step0; decide +kernel
      have hl : raw10662step1Labels = raw10662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10662step0 raw10662step0Labels permutation56 hz
    mixedMoment B raw10662step1 raw10662step1Labels = mixedMoment B raw10662step2 raw10662step2Labels := by
      have ha : raw10662step2 = (fun i j => raw10662step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10662step2 raw10662step1; decide +kernel
      have hl : raw10662step2Labels = raw10662step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10662step1 raw10662step1Labels permutation31 permutation7
    mixedMoment B raw10662step2 raw10662step2Labels = mixedMoment B raw10662step3 raw10662step3Labels := by
      have ha : raw10662step3 = raw10662step2 := by apply Matrix.ext; unfold raw10662step3 raw10662step2; decide +kernel
      have hl : raw10662step2Labels = labelEmbedding1 ∘ raw10662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10662step2 raw10662step2Labels raw10662step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw10663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10663Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10663step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10663step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10663 raw10663Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw10663 raw10663Labels = mixedMoment B raw10663step0 raw10663step0Labels := by
      have hz : ∀ j, raw10663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10663step0 = (fun i j => raw10663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10663step0 raw10663; decide +kernel
      have hl : raw10663step0Labels = raw10663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10663 raw10663Labels permutation346 hz
    mixedMoment B raw10663step0 raw10663step0Labels = mixedMoment B raw10663step1 raw10663step1Labels := by
      have ha : raw10663step1 = (fun i j => raw10663step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10663step1 raw10663step0; decide +kernel
      have hl : raw10663step1Labels = raw10663step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10663step0 raw10663step0Labels permutation149 permutation7
    mixedMoment B raw10663step1 raw10663step1Labels = mixedMoment B raw10663step2 raw10663step2Labels := by
      have ha : raw10663step2 = raw10663step1 := by apply Matrix.ext; unfold raw10663step2 raw10663step1; decide +kernel
      have hl : raw10663step1Labels = labelEmbedding1 ∘ raw10663step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10663step1 raw10663step1Labels raw10663step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw10664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10664Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10664step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10664step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10664 raw10664Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw10664 raw10664Labels = mixedMoment B raw10664step0 raw10664step0Labels := by
      have hz : ∀ j, raw10664 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10664step0 = (fun i j => raw10664 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10664step0 raw10664; decide +kernel
      have hl : raw10664step0Labels = raw10664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10664 raw10664Labels permutation265 hz
    mixedMoment B raw10664step0 raw10664step0Labels = mixedMoment B raw10664step1 raw10664step1Labels := by
      have ha : raw10664step1 = (fun i j => raw10664step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10664step1 raw10664step0; decide +kernel
      have hl : raw10664step1Labels = raw10664step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10664step0 raw10664step0Labels permutation149 permutation7
    mixedMoment B raw10664step1 raw10664step1Labels = mixedMoment B raw10664step2 raw10664step2Labels := by
      have ha : raw10664step2 = raw10664step1 := by apply Matrix.ext; unfold raw10664step2 raw10664step1; decide +kernel
      have hl : raw10664step1Labels = labelEmbedding1 ∘ raw10664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10664step1 raw10664step1Labels raw10664step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw10665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10665Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10665step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10665step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw10665step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw10665step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10665 raw10665Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw10665 raw10665Labels = mixedMoment B raw10665step0 raw10665step0Labels := by
      have hz : ∀ j, raw10665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10665step0 = (fun i j => raw10665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10665step0 raw10665; decide +kernel
      have hl : raw10665step0Labels = raw10665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10665 raw10665Labels permutation346 hz
    mixedMoment B raw10665step0 raw10665step0Labels = mixedMoment B raw10665step1 raw10665step1Labels := by
      have hz : ∀ j, raw10665step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10665step1 = (fun i j => raw10665step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10665step1 raw10665step0; decide +kernel
      have hl : raw10665step1Labels = raw10665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10665step0 raw10665step0Labels permutation56 hz
    mixedMoment B raw10665step1 raw10665step1Labels = mixedMoment B raw10665step2 raw10665step2Labels := by
      have ha : raw10665step2 = (fun i j => raw10665step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10665step2 raw10665step1; decide +kernel
      have hl : raw10665step2Labels = raw10665step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10665step1 raw10665step1Labels permutation31 permutation7
    mixedMoment B raw10665step2 raw10665step2Labels = mixedMoment B raw10665step3 raw10665step3Labels := by
      have ha : raw10665step3 = raw10665step2 := by apply Matrix.ext; unfold raw10665step3 raw10665step2; decide +kernel
      have hl : raw10665step2Labels = labelEmbedding1 ∘ raw10665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10665step2 raw10665step2Labels raw10665step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw10666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10666Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10666step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10666step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw10666step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw10666step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10666 raw10666Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw10666 raw10666Labels = mixedMoment B raw10666step0 raw10666step0Labels := by
      have hz : ∀ j, raw10666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10666step0 = (fun i j => raw10666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10666step0 raw10666; decide +kernel
      have hl : raw10666step0Labels = raw10666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10666 raw10666Labels permutation346 hz
    mixedMoment B raw10666step0 raw10666step0Labels = mixedMoment B raw10666step1 raw10666step1Labels := by
      have hz : ∀ j, raw10666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10666step1 = (fun i j => raw10666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10666step1 raw10666step0; decide +kernel
      have hl : raw10666step1Labels = raw10666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10666step0 raw10666step0Labels permutation56 hz
    mixedMoment B raw10666step1 raw10666step1Labels = mixedMoment B raw10666step2 raw10666step2Labels := by
      have ha : raw10666step2 = (fun i j => raw10666step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10666step2 raw10666step1; decide +kernel
      have hl : raw10666step2Labels = raw10666step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10666step1 raw10666step1Labels permutation31 permutation7
    mixedMoment B raw10666step2 raw10666step2Labels = mixedMoment B raw10666step3 raw10666step3Labels := by
      have ha : raw10666step3 = raw10666step2 := by apply Matrix.ext; unfold raw10666step3 raw10666step2; decide +kernel
      have hl : raw10666step2Labels = labelEmbedding1 ∘ raw10666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10666step2 raw10666step2Labels raw10666step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw10667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10667Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10667step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10667step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10667step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw10667step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10667 raw10667Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw10667 raw10667Labels = mixedMoment B raw10667step0 raw10667step0Labels := by
      have hz : ∀ j, raw10667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10667step0 = (fun i j => raw10667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10667step0 raw10667; decide +kernel
      have hl : raw10667step0Labels = raw10667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10667 raw10667Labels permutation346 hz
    mixedMoment B raw10667step0 raw10667step0Labels = mixedMoment B raw10667step1 raw10667step1Labels := by
      have hz : ∀ j, raw10667step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10667step1 = (fun i j => raw10667step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10667step1 raw10667step0; decide +kernel
      have hl : raw10667step1Labels = raw10667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10667step0 raw10667step0Labels permutation56 hz
    mixedMoment B raw10667step1 raw10667step1Labels = mixedMoment B raw10667step2 raw10667step2Labels := by
      have ha : raw10667step2 = (fun i j => raw10667step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10667step2 raw10667step1; decide +kernel
      have hl : raw10667step2Labels = raw10667step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10667step1 raw10667step1Labels permutation31 permutation7
    mixedMoment B raw10667step2 raw10667step2Labels = mixedMoment B raw10667step3 raw10667step3Labels := by
      have ha : raw10667step3 = raw10667step2 := by apply Matrix.ext; unfold raw10667step3 raw10667step2; decide +kernel
      have hl : raw10667step2Labels = labelEmbedding1 ∘ raw10667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10667step2 raw10667step2Labels raw10667step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw10668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10668Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10668step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10668 raw10668Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw10668 raw10668Labels = mixedMoment B raw10668step0 raw10668step0Labels := by
      have hz : ∀ j, raw10668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10668step0 = (fun i j => raw10668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10668step0 raw10668; decide +kernel
      have hl : raw10668step0Labels = raw10668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10668 raw10668Labels permutation346 hz
    mixedMoment B raw10668step0 raw10668step0Labels = mixedMoment B raw10668step1 raw10668step1Labels := by
      have ha : raw10668step1 = (fun i j => raw10668step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10668step1 raw10668step0; decide +kernel
      have hl : raw10668step1Labels = raw10668step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10668step0 raw10668step0Labels permutation149 permutation7
    mixedMoment B raw10668step1 raw10668step1Labels = mixedMoment B raw10668step2 raw10668step2Labels := by
      have ha : raw10668step2 = raw10668step1 := by apply Matrix.ext; unfold raw10668step2 raw10668step1; decide +kernel
      have hl : raw10668step1Labels = labelEmbedding1 ∘ raw10668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10668step1 raw10668step1Labels raw10668step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw10669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10669Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10669step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10669step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10669 raw10669Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw10669 raw10669Labels = mixedMoment B raw10669step0 raw10669step0Labels := by
      have hz : ∀ j, raw10669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10669step0 = (fun i j => raw10669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10669step0 raw10669; decide +kernel
      have hl : raw10669step0Labels = raw10669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10669 raw10669Labels permutation265 hz
    mixedMoment B raw10669step0 raw10669step0Labels = mixedMoment B raw10669step1 raw10669step1Labels := by
      have ha : raw10669step1 = (fun i j => raw10669step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10669step1 raw10669step0; decide +kernel
      have hl : raw10669step1Labels = raw10669step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10669step0 raw10669step0Labels permutation149 permutation7
    mixedMoment B raw10669step1 raw10669step1Labels = mixedMoment B raw10669step2 raw10669step2Labels := by
      have ha : raw10669step2 = raw10669step1 := by apply Matrix.ext; unfold raw10669step2 raw10669step1; decide +kernel
      have hl : raw10669step1Labels = labelEmbedding1 ∘ raw10669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10669step1 raw10669step1Labels raw10669step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw10670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10670Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10670step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10670step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10670step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10670step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10670step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10670 raw10670Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw10670 raw10670Labels = mixedMoment B raw10670step0 raw10670step0Labels := by
      have hz : ∀ j, raw10670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10670step0 = (fun i j => raw10670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10670step0 raw10670; decide +kernel
      have hl : raw10670step0Labels = raw10670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10670 raw10670Labels permutation346 hz
    mixedMoment B raw10670step0 raw10670step0Labels = mixedMoment B raw10670step1 raw10670step1Labels := by
      have hz : ∀ j, raw10670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10670step1 = (fun i j => raw10670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10670step1 raw10670step0; decide +kernel
      have hl : raw10670step1Labels = raw10670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10670step0 raw10670step0Labels permutation56 hz
    mixedMoment B raw10670step1 raw10670step1Labels = mixedMoment B raw10670step2 raw10670step2Labels := by
      have ha : raw10670step2 = (fun i j => raw10670step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10670step2 raw10670step1; decide +kernel
      have hl : raw10670step2Labels = raw10670step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10670step1 raw10670step1Labels permutation31 permutation7
    mixedMoment B raw10670step2 raw10670step2Labels = mixedMoment B raw10670step3 raw10670step3Labels := by
      have ha : raw10670step3 = raw10670step2 := by apply Matrix.ext; unfold raw10670step3 raw10670step2; decide +kernel
      have hl : raw10670step2Labels = labelEmbedding1 ∘ raw10670step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10670step2 raw10670step2Labels raw10670step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw10671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw10671Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10671step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10671step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10671step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10671step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10671step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw10671step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10671step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw10671step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10671 raw10671Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw10671 raw10671Labels = mixedMoment B raw10671step0 raw10671step0Labels := by
      have hz : ∀ j, raw10671 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10671step0 = (fun i j => raw10671 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10671step0 raw10671; decide +kernel
      have hl : raw10671step0Labels = raw10671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671 raw10671Labels permutation520 hz
    mixedMoment B raw10671step0 raw10671step0Labels = mixedMoment B raw10671step1 raw10671step1Labels := by
      have hz : ∀ j, raw10671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10671step1 = (fun i j => raw10671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10671step1 raw10671step0; decide +kernel
      have hl : raw10671step1Labels = raw10671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671step0 raw10671step0Labels permutation80 hz
    mixedMoment B raw10671step1 raw10671step1Labels = mixedMoment B raw10671step2 raw10671step2Labels := by
      have hz : ∀ j, raw10671step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10671step2 = (fun i j => raw10671step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10671step2 raw10671step1; decide +kernel
      have hl : raw10671step2Labels = raw10671step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671step1 raw10671step1Labels permutation14 hz
    mixedMoment B raw10671step2 raw10671step2Labels = mixedMoment B raw10671step3 raw10671step3Labels := by
      have ha : raw10671step3 = (fun i j => raw10671step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10671step3 raw10671step2; decide +kernel
      have hl : raw10671step3Labels = raw10671step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10671step2 raw10671step2Labels permutation7 permutation7
    mixedMoment B raw10671step3 raw10671step3Labels = mixedMoment B raw10671step4 raw10671step4Labels := by
      have ha : raw10671step4 = raw10671step3 := by apply Matrix.ext; unfold raw10671step4 raw10671step3; decide +kernel
      have hl : raw10671step3Labels = labelEmbedding1 ∘ raw10671step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10671step3 raw10671step3Labels raw10671step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

def raw10672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10672step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10672step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10672 raw10672Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10672 raw10672Labels = mixedMoment B raw10672step0 raw10672step0Labels := by
      have hz : ∀ j, raw10672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10672step0 = (fun i j => raw10672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10672step0 raw10672; decide +kernel
      have hl : raw10672step0Labels = raw10672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10672 raw10672Labels permutation346 hz
    mixedMoment B raw10672step0 raw10672step0Labels = mixedMoment B raw10672step1 raw10672step1Labels := by
      have ha : raw10672step1 = (fun i j => raw10672step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10672step1 raw10672step0; decide +kernel
      have hl : raw10672step1Labels = raw10672step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10672step0 raw10672step0Labels permutation151 permutation5
    mixedMoment B raw10672step1 raw10672step1Labels = mixedMoment B raw10672step2 raw10672step2Labels := by
      have ha : raw10672step2 = raw10672step1 := by apply Matrix.ext; unfold raw10672step2 raw10672step1; decide +kernel
      have hl : raw10672step1Labels = labelEmbedding8 ∘ raw10672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10672step1 raw10672step1Labels raw10672step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10673step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10673 raw10673Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10673 raw10673Labels = mixedMoment B raw10673step0 raw10673step0Labels := by
      have hz : ∀ j, raw10673 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10673step0 = (fun i j => raw10673 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10673step0 raw10673; decide +kernel
      have hl : raw10673step0Labels = raw10673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10673 raw10673Labels permutation265 hz
    mixedMoment B raw10673step0 raw10673step0Labels = mixedMoment B raw10673step1 raw10673step1Labels := by
      have ha : raw10673step1 = (fun i j => raw10673step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10673step1 raw10673step0; decide +kernel
      have hl : raw10673step1Labels = raw10673step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10673step0 raw10673step0Labels permutation151 permutation5
    mixedMoment B raw10673step1 raw10673step1Labels = mixedMoment B raw10673step2 raw10673step2Labels := by
      have ha : raw10673step2 = raw10673step1 := by apply Matrix.ext; unfold raw10673step2 raw10673step1; decide +kernel
      have hl : raw10673step1Labels = labelEmbedding8 ∘ raw10673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10673step1 raw10673step1Labels raw10673step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10674step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10674step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10674 raw10674Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw10674 raw10674Labels = mixedMoment B raw10674step0 raw10674step0Labels := by
      have hz : ∀ j, raw10674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10674step0 = (fun i j => raw10674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10674step0 raw10674; decide +kernel
      have hl : raw10674step0Labels = raw10674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10674 raw10674Labels permutation346 hz
    mixedMoment B raw10674step0 raw10674step0Labels = mixedMoment B raw10674step1 raw10674step1Labels := by
      have hz : ∀ j, raw10674step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10674step1 = (fun i j => raw10674step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10674step1 raw10674step0; decide +kernel
      have hl : raw10674step1Labels = raw10674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10674step0 raw10674step0Labels permutation56 hz
    mixedMoment B raw10674step1 raw10674step1Labels = mixedMoment B raw10674step2 raw10674step2Labels := by
      have ha : raw10674step2 = (fun i j => raw10674step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10674step2 raw10674step1; decide +kernel
      have hl : raw10674step2Labels = raw10674step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10674step1 raw10674step1Labels permutation30 permutation5
    mixedMoment B raw10674step2 raw10674step2Labels = mixedMoment B raw10674step3 raw10674step3Labels := by
      have ha : raw10674step3 = raw10674step2 := by apply Matrix.ext; unfold raw10674step3 raw10674step2; decide +kernel
      have hl : raw10674step2Labels = labelEmbedding8 ∘ raw10674step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10674step2 raw10674step2Labels raw10674step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw10675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10675step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10675 raw10675Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw10675 raw10675Labels = mixedMoment B raw10675step0 raw10675step0Labels := by
      have hz : ∀ j, raw10675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10675step0 = (fun i j => raw10675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10675step0 raw10675; decide +kernel
      have hl : raw10675step0Labels = raw10675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10675 raw10675Labels permutation346 hz
    mixedMoment B raw10675step0 raw10675step0Labels = mixedMoment B raw10675step1 raw10675step1Labels := by
      have hz : ∀ j, raw10675step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10675step1 = (fun i j => raw10675step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10675step1 raw10675step0; decide +kernel
      have hl : raw10675step1Labels = raw10675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10675step0 raw10675step0Labels permutation56 hz
    mixedMoment B raw10675step1 raw10675step1Labels = mixedMoment B raw10675step2 raw10675step2Labels := by
      have ha : raw10675step2 = (fun i j => raw10675step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10675step2 raw10675step1; decide +kernel
      have hl : raw10675step2Labels = raw10675step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10675step1 raw10675step1Labels permutation29 permutation5
    mixedMoment B raw10675step2 raw10675step2Labels = mixedMoment B raw10675step3 raw10675step3Labels := by
      have ha : raw10675step3 = raw10675step2 := by apply Matrix.ext; unfold raw10675step3 raw10675step2; decide +kernel
      have hl : raw10675step2Labels = labelEmbedding8 ∘ raw10675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10675step2 raw10675step2Labels raw10675step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw10676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10676step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10676step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10676 raw10676Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw10676 raw10676Labels = mixedMoment B raw10676step0 raw10676step0Labels := by
      have hz : ∀ j, raw10676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10676step0 = (fun i j => raw10676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10676step0 raw10676; decide +kernel
      have hl : raw10676step0Labels = raw10676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10676 raw10676Labels permutation346 hz
    mixedMoment B raw10676step0 raw10676step0Labels = mixedMoment B raw10676step1 raw10676step1Labels := by
      have hz : ∀ j, raw10676step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10676step1 = (fun i j => raw10676step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10676step1 raw10676step0; decide +kernel
      have hl : raw10676step1Labels = raw10676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10676step0 raw10676step0Labels permutation56 hz
    mixedMoment B raw10676step1 raw10676step1Labels = mixedMoment B raw10676step2 raw10676step2Labels := by
      have ha : raw10676step2 = (fun i j => raw10676step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10676step2 raw10676step1; decide +kernel
      have hl : raw10676step2Labels = raw10676step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10676step1 raw10676step1Labels permutation8 permutation3
    mixedMoment B raw10676step2 raw10676step2Labels = mixedMoment B raw10676step3 raw10676step3Labels := by
      have ha : raw10676step3 = raw10676step2 := by apply Matrix.ext; unfold raw10676step3 raw10676step2; decide +kernel
      have hl : raw10676step2Labels = labelEmbedding6 ∘ raw10676step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10676step2 raw10676step2Labels raw10676step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw10677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10677 raw10677Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw10677 raw10677Labels = mixedMoment B raw10677step0 raw10677step0Labels := by
      have hz : ∀ j, raw10677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10677step0 = (fun i j => raw10677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10677step0 raw10677; decide +kernel
      have hl : raw10677step0Labels = raw10677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10677 raw10677Labels permutation346 hz
    mixedMoment B raw10677step0 raw10677step0Labels = mixedMoment B raw10677step1 raw10677step1Labels := by
      have ha : raw10677step1 = (fun i j => raw10677step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10677step1 raw10677step0; decide +kernel
      have hl : raw10677step1Labels = raw10677step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10677step0 raw10677step0Labels permutation40 permutation3
    mixedMoment B raw10677step1 raw10677step1Labels = mixedMoment B raw10677step2 raw10677step2Labels := by
      have ha : raw10677step2 = raw10677step1 := by apply Matrix.ext; unfold raw10677step2 raw10677step1; decide +kernel
      have hl : raw10677step1Labels = labelEmbedding6 ∘ raw10677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10677step1 raw10677step1Labels raw10677step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw10678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10678step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10678 raw10678Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw10678 raw10678Labels = mixedMoment B raw10678step0 raw10678step0Labels := by
      have ha : raw10678step0 = (fun i j => raw10678 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10678step0 raw10678; decide +kernel
      have hl : raw10678step0Labels = raw10678Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10678 raw10678Labels permutation184 permutation3
    mixedMoment B raw10678step0 raw10678step0Labels = mixedMoment B raw10678step1 raw10678step1Labels := by
      have ha : raw10678step1 = raw10678step0 := by apply Matrix.ext; unfold raw10678step1 raw10678step0; decide +kernel
      have hl : raw10678step0Labels = labelEmbedding6 ∘ raw10678step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10678step0 raw10678step0Labels raw10678step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw10679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10679step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10679 raw10679Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw10679 raw10679Labels = mixedMoment B raw10679step0 raw10679step0Labels := by
      have hz : ∀ j, raw10679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10679step0 = (fun i j => raw10679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10679step0 raw10679; decide +kernel
      have hl : raw10679step0Labels = raw10679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10679 raw10679Labels permutation346 hz
    mixedMoment B raw10679step0 raw10679step0Labels = mixedMoment B raw10679step1 raw10679step1Labels := by
      have ha : raw10679step1 = (fun i j => raw10679step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10679step1 raw10679step0; decide +kernel
      have hl : raw10679step1Labels = raw10679step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10679step0 raw10679step0Labels permutation40 permutation3
    mixedMoment B raw10679step1 raw10679step1Labels = mixedMoment B raw10679step2 raw10679step2Labels := by
      have ha : raw10679step2 = raw10679step1 := by apply Matrix.ext; unfold raw10679step2 raw10679step1; decide +kernel
      have hl : raw10679step1Labels = labelEmbedding6 ∘ raw10679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10679step1 raw10679step1Labels raw10679step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw10680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10680step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10680 raw10680Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw10680 raw10680Labels = mixedMoment B raw10680step0 raw10680step0Labels := by
      have hz : ∀ j, raw10680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10680step0 = (fun i j => raw10680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10680step0 raw10680; decide +kernel
      have hl : raw10680step0Labels = raw10680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10680 raw10680Labels permutation346 hz
    mixedMoment B raw10680step0 raw10680step0Labels = mixedMoment B raw10680step1 raw10680step1Labels := by
      have ha : raw10680step1 = (fun i j => raw10680step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10680step1 raw10680step0; decide +kernel
      have hl : raw10680step1Labels = raw10680step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10680step0 raw10680step0Labels permutation137 permutation5
    mixedMoment B raw10680step1 raw10680step1Labels = mixedMoment B raw10680step2 raw10680step2Labels := by
      have ha : raw10680step2 = raw10680step1 := by apply Matrix.ext; unfold raw10680step2 raw10680step1; decide +kernel
      have hl : raw10680step1Labels = labelEmbedding8 ∘ raw10680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10680step1 raw10680step1Labels raw10680step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw10681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10681step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10681 raw10681Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10681 raw10681Labels = mixedMoment B raw10681step0 raw10681step0Labels := by
      have hz : ∀ j, raw10681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10681step0 = (fun i j => raw10681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10681step0 raw10681; decide +kernel
      have hl : raw10681step0Labels = raw10681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10681 raw10681Labels permutation346 hz
    mixedMoment B raw10681step0 raw10681step0Labels = mixedMoment B raw10681step1 raw10681step1Labels := by
      have ha : raw10681step1 = (fun i j => raw10681step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10681step1 raw10681step0; decide +kernel
      have hl : raw10681step1Labels = raw10681step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10681step0 raw10681step0Labels permutation40 permutation3
    mixedMoment B raw10681step1 raw10681step1Labels = mixedMoment B raw10681step2 raw10681step2Labels := by
      have ha : raw10681step2 = raw10681step1 := by apply Matrix.ext; unfold raw10681step2 raw10681step1; decide +kernel
      have hl : raw10681step1Labels = labelEmbedding6 ∘ raw10681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10681step1 raw10681step1Labels raw10681step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10682step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10682 raw10682Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw10682 raw10682Labels = mixedMoment B raw10682step0 raw10682step0Labels := by
      have hz : ∀ j, raw10682 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10682step0 = (fun i j => raw10682 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10682step0 raw10682; decide +kernel
      have hl : raw10682step0Labels = raw10682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10682 raw10682Labels permutation265 hz
    mixedMoment B raw10682step0 raw10682step0Labels = mixedMoment B raw10682step1 raw10682step1Labels := by
      have ha : raw10682step1 = (fun i j => raw10682step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10682step1 raw10682step0; decide +kernel
      have hl : raw10682step1Labels = raw10682step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10682step0 raw10682step0Labels permutation40 permutation3
    mixedMoment B raw10682step1 raw10682step1Labels = mixedMoment B raw10682step2 raw10682step2Labels := by
      have ha : raw10682step2 = raw10682step1 := by apply Matrix.ext; unfold raw10682step2 raw10682step1; decide +kernel
      have hl : raw10682step1Labels = labelEmbedding6 ∘ raw10682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10682step1 raw10682step1Labels raw10682step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw10683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10683step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10683 raw10683Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw10683 raw10683Labels = mixedMoment B raw10683step0 raw10683step0Labels := by
      have ha : raw10683step0 = (fun i j => raw10683 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10683step0 raw10683; decide +kernel
      have hl : raw10683step0Labels = raw10683Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10683 raw10683Labels permutation160 permutation3
    mixedMoment B raw10683step0 raw10683step0Labels = mixedMoment B raw10683step1 raw10683step1Labels := by
      have ha : raw10683step1 = raw10683step0 := by apply Matrix.ext; unfold raw10683step1 raw10683step0; decide +kernel
      have hl : raw10683step0Labels = labelEmbedding6 ∘ raw10683step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10683step0 raw10683step0Labels raw10683step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw10684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10684step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10684 raw10684Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw10684 raw10684Labels = mixedMoment B raw10684step0 raw10684step0Labels := by
      have hz : ∀ j, raw10684 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10684step0 = (fun i j => raw10684 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10684step0 raw10684; decide +kernel
      have hl : raw10684step0Labels = raw10684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10684 raw10684Labels permutation265 hz
    mixedMoment B raw10684step0 raw10684step0Labels = mixedMoment B raw10684step1 raw10684step1Labels := by
      have ha : raw10684step1 = (fun i j => raw10684step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10684step1 raw10684step0; decide +kernel
      have hl : raw10684step1Labels = raw10684step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10684step0 raw10684step0Labels permutation40 permutation3
    mixedMoment B raw10684step1 raw10684step1Labels = mixedMoment B raw10684step2 raw10684step2Labels := by
      have ha : raw10684step2 = raw10684step1 := by apply Matrix.ext; unfold raw10684step2 raw10684step1; decide +kernel
      have hl : raw10684step1Labels = labelEmbedding6 ∘ raw10684step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10684step1 raw10684step1Labels raw10684step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw10685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10685step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10685 raw10685Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw10685 raw10685Labels = mixedMoment B raw10685step0 raw10685step0Labels := by
      have hz : ∀ j, raw10685 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10685step0 = (fun i j => raw10685 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10685step0 raw10685; decide +kernel
      have hl : raw10685step0Labels = raw10685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10685 raw10685Labels permutation265 hz
    mixedMoment B raw10685step0 raw10685step0Labels = mixedMoment B raw10685step1 raw10685step1Labels := by
      have ha : raw10685step1 = (fun i j => raw10685step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10685step1 raw10685step0; decide +kernel
      have hl : raw10685step1Labels = raw10685step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10685step0 raw10685step0Labels permutation137 permutation5
    mixedMoment B raw10685step1 raw10685step1Labels = mixedMoment B raw10685step2 raw10685step2Labels := by
      have ha : raw10685step2 = raw10685step1 := by apply Matrix.ext; unfold raw10685step2 raw10685step1; decide +kernel
      have hl : raw10685step1Labels = labelEmbedding8 ∘ raw10685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10685step1 raw10685step1Labels raw10685step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw10686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10686step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10686 raw10686Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10686 raw10686Labels = mixedMoment B raw10686step0 raw10686step0Labels := by
      have hz : ∀ j, raw10686 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10686step0 = (fun i j => raw10686 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10686step0 raw10686; decide +kernel
      have hl : raw10686step0Labels = raw10686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10686 raw10686Labels permutation265 hz
    mixedMoment B raw10686step0 raw10686step0Labels = mixedMoment B raw10686step1 raw10686step1Labels := by
      have ha : raw10686step1 = (fun i j => raw10686step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10686step1 raw10686step0; decide +kernel
      have hl : raw10686step1Labels = raw10686step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10686step0 raw10686step0Labels permutation40 permutation3
    mixedMoment B raw10686step1 raw10686step1Labels = mixedMoment B raw10686step2 raw10686step2Labels := by
      have ha : raw10686step2 = raw10686step1 := by apply Matrix.ext; unfold raw10686step2 raw10686step1; decide +kernel
      have hl : raw10686step1Labels = labelEmbedding6 ∘ raw10686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10686step1 raw10686step1Labels raw10686step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10687step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10687step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10687 raw10687Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw10687 raw10687Labels = mixedMoment B raw10687step0 raw10687step0Labels := by
      have hz : ∀ j, raw10687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10687step0 = (fun i j => raw10687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10687step0 raw10687; decide +kernel
      have hl : raw10687step0Labels = raw10687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10687 raw10687Labels permutation346 hz
    mixedMoment B raw10687step0 raw10687step0Labels = mixedMoment B raw10687step1 raw10687step1Labels := by
      have hz : ∀ j, raw10687step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10687step1 = (fun i j => raw10687step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10687step1 raw10687step0; decide +kernel
      have hl : raw10687step1Labels = raw10687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10687step0 raw10687step0Labels permutation56 hz
    mixedMoment B raw10687step1 raw10687step1Labels = mixedMoment B raw10687step2 raw10687step2Labels := by
      have ha : raw10687step2 = (fun i j => raw10687step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10687step2 raw10687step1; decide +kernel
      have hl : raw10687step2Labels = raw10687step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10687step1 raw10687step1Labels permutation8 permutation3
    mixedMoment B raw10687step2 raw10687step2Labels = mixedMoment B raw10687step3 raw10687step3Labels := by
      have ha : raw10687step3 = raw10687step2 := by apply Matrix.ext; unfold raw10687step3 raw10687step2; decide +kernel
      have hl : raw10687step2Labels = labelEmbedding6 ∘ raw10687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10687step2 raw10687step2Labels raw10687step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw10688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10688step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10688 raw10688Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw10688 raw10688Labels = mixedMoment B raw10688step0 raw10688step0Labels := by
      have hz : ∀ j, raw10688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10688step0 = (fun i j => raw10688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10688step0 raw10688; decide +kernel
      have hl : raw10688step0Labels = raw10688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10688 raw10688Labels permutation346 hz
    mixedMoment B raw10688step0 raw10688step0Labels = mixedMoment B raw10688step1 raw10688step1Labels := by
      have ha : raw10688step1 = (fun i j => raw10688step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10688step1 raw10688step0; decide +kernel
      have hl : raw10688step1Labels = raw10688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10688step0 raw10688step0Labels permutation32 permutation3
    mixedMoment B raw10688step1 raw10688step1Labels = mixedMoment B raw10688step2 raw10688step2Labels := by
      have ha : raw10688step2 = raw10688step1 := by apply Matrix.ext; unfold raw10688step2 raw10688step1; decide +kernel
      have hl : raw10688step1Labels = labelEmbedding6 ∘ raw10688step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10688step1 raw10688step1Labels raw10688step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw10689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10689step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10689 raw10689Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw10689 raw10689Labels = mixedMoment B raw10689step0 raw10689step0Labels := by
      have hz : ∀ j, raw10689 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10689step0 = (fun i j => raw10689 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10689step0 raw10689; decide +kernel
      have hl : raw10689step0Labels = raw10689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10689 raw10689Labels permutation265 hz
    mixedMoment B raw10689step0 raw10689step0Labels = mixedMoment B raw10689step1 raw10689step1Labels := by
      have ha : raw10689step1 = (fun i j => raw10689step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10689step1 raw10689step0; decide +kernel
      have hl : raw10689step1Labels = raw10689step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10689step0 raw10689step0Labels permutation32 permutation3
    mixedMoment B raw10689step1 raw10689step1Labels = mixedMoment B raw10689step2 raw10689step2Labels := by
      have ha : raw10689step2 = raw10689step1 := by apply Matrix.ext; unfold raw10689step2 raw10689step1; decide +kernel
      have hl : raw10689step1Labels = labelEmbedding6 ∘ raw10689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10689step1 raw10689step1Labels raw10689step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw10690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw10690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10690step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10690 raw10690Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw10690 raw10690Labels = mixedMoment B raw10690step0 raw10690step0Labels := by
      have hz : ∀ j, raw10690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10690step0 = (fun i j => raw10690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10690step0 raw10690; decide +kernel
      have hl : raw10690step0Labels = raw10690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10690 raw10690Labels permutation346 hz
    mixedMoment B raw10690step0 raw10690step0Labels = mixedMoment B raw10690step1 raw10690step1Labels := by
      have hz : ∀ j, raw10690step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10690step1 = (fun i j => raw10690step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10690step1 raw10690step0; decide +kernel
      have hl : raw10690step1Labels = raw10690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10690step0 raw10690step0Labels permutation56 hz
    mixedMoment B raw10690step1 raw10690step1Labels = mixedMoment B raw10690step2 raw10690step2Labels := by
      have ha : raw10690step2 = (fun i j => raw10690step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10690step2 raw10690step1; decide +kernel
      have hl : raw10690step2Labels = raw10690step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10690step1 raw10690step1Labels permutation10 permutation3
    mixedMoment B raw10690step2 raw10690step2Labels = mixedMoment B raw10690step3 raw10690step3Labels := by
      have ha : raw10690step3 = raw10690step2 := by apply Matrix.ext; unfold raw10690step3 raw10690step2; decide +kernel
      have hl : raw10690step2Labels = labelEmbedding6 ∘ raw10690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10690step2 raw10690step2Labels raw10690step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw10691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw10691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10691step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10691step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10691step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10691 raw10691Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw10691 raw10691Labels = mixedMoment B raw10691step0 raw10691step0Labels := by
      have hz : ∀ j, raw10691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10691step0 = (fun i j => raw10691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10691step0 raw10691; decide +kernel
      have hl : raw10691step0Labels = raw10691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10691 raw10691Labels permutation346 hz
    mixedMoment B raw10691step0 raw10691step0Labels = mixedMoment B raw10691step1 raw10691step1Labels := by
      have hz : ∀ j, raw10691step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10691step1 = (fun i j => raw10691step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10691step1 raw10691step0; decide +kernel
      have hl : raw10691step1Labels = raw10691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10691step0 raw10691step0Labels permutation56 hz
    mixedMoment B raw10691step1 raw10691step1Labels = mixedMoment B raw10691step2 raw10691step2Labels := by
      have ha : raw10691step2 = (fun i j => raw10691step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10691step2 raw10691step1; decide +kernel
      have hl : raw10691step2Labels = raw10691step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10691step1 raw10691step1Labels permutation8 permutation3
    mixedMoment B raw10691step2 raw10691step2Labels = mixedMoment B raw10691step3 raw10691step3Labels := by
      have ha : raw10691step3 = raw10691step2 := by apply Matrix.ext; unfold raw10691step3 raw10691step2; decide +kernel
      have hl : raw10691step2Labels = labelEmbedding6 ∘ raw10691step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10691step2 raw10691step2Labels raw10691step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw10692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10692step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10692step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10692step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10692 raw10692Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw10692 raw10692Labels = mixedMoment B raw10692step0 raw10692step0Labels := by
      have hz : ∀ j, raw10692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10692step0 = (fun i j => raw10692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10692step0 raw10692; decide +kernel
      have hl : raw10692step0Labels = raw10692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10692 raw10692Labels permutation346 hz
    mixedMoment B raw10692step0 raw10692step0Labels = mixedMoment B raw10692step1 raw10692step1Labels := by
      have hz : ∀ j, raw10692step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10692step1 = (fun i j => raw10692step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10692step1 raw10692step0; decide +kernel
      have hl : raw10692step1Labels = raw10692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10692step0 raw10692step0Labels permutation56 hz
    mixedMoment B raw10692step1 raw10692step1Labels = mixedMoment B raw10692step2 raw10692step2Labels := by
      have ha : raw10692step2 = (fun i j => raw10692step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10692step2 raw10692step1; decide +kernel
      have hl : raw10692step2Labels = raw10692step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10692step1 raw10692step1Labels permutation8 permutation3
    mixedMoment B raw10692step2 raw10692step2Labels = mixedMoment B raw10692step3 raw10692step3Labels := by
      have ha : raw10692step3 = raw10692step2 := by apply Matrix.ext; unfold raw10692step3 raw10692step2; decide +kernel
      have hl : raw10692step2Labels = labelEmbedding6 ∘ raw10692step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10692step2 raw10692step2Labels raw10692step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw10693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10693step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10693 raw10693Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw10693 raw10693Labels = mixedMoment B raw10693step0 raw10693step0Labels := by
      have hz : ∀ j, raw10693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10693step0 = (fun i j => raw10693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10693step0 raw10693; decide +kernel
      have hl : raw10693step0Labels = raw10693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10693 raw10693Labels permutation346 hz
    mixedMoment B raw10693step0 raw10693step0Labels = mixedMoment B raw10693step1 raw10693step1Labels := by
      have ha : raw10693step1 = (fun i j => raw10693step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10693step1 raw10693step0; decide +kernel
      have hl : raw10693step1Labels = raw10693step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10693step0 raw10693step0Labels permutation151 permutation5
    mixedMoment B raw10693step1 raw10693step1Labels = mixedMoment B raw10693step2 raw10693step2Labels := by
      have ha : raw10693step2 = raw10693step1 := by apply Matrix.ext; unfold raw10693step2 raw10693step1; decide +kernel
      have hl : raw10693step1Labels = labelEmbedding8 ∘ raw10693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10693step1 raw10693step1Labels raw10693step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw10694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10694step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10694 raw10694Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw10694 raw10694Labels = mixedMoment B raw10694step0 raw10694step0Labels := by
      have hz : ∀ j, raw10694 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10694step0 = (fun i j => raw10694 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10694step0 raw10694; decide +kernel
      have hl : raw10694step0Labels = raw10694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10694 raw10694Labels permutation265 hz
    mixedMoment B raw10694step0 raw10694step0Labels = mixedMoment B raw10694step1 raw10694step1Labels := by
      have ha : raw10694step1 = (fun i j => raw10694step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10694step1 raw10694step0; decide +kernel
      have hl : raw10694step1Labels = raw10694step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10694step0 raw10694step0Labels permutation151 permutation5
    mixedMoment B raw10694step1 raw10694step1Labels = mixedMoment B raw10694step2 raw10694step2Labels := by
      have ha : raw10694step2 = raw10694step1 := by apply Matrix.ext; unfold raw10694step2 raw10694step1; decide +kernel
      have hl : raw10694step1Labels = labelEmbedding8 ∘ raw10694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10694step1 raw10694step1Labels raw10694step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw10695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw10695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw10695step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw10695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10695 raw10695Labels = mixedMoment B node5023 node5023Labels := by
  calc
    mixedMoment B raw10695 raw10695Labels = mixedMoment B raw10695step0 raw10695step0Labels := by
      have hz : ∀ j, raw10695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10695step0 = (fun i j => raw10695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10695step0 raw10695; decide +kernel
      have hl : raw10695step0Labels = raw10695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10695 raw10695Labels permutation346 hz
    mixedMoment B raw10695step0 raw10695step0Labels = mixedMoment B raw10695step1 raw10695step1Labels := by
      have hz : ∀ j, raw10695step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10695step1 = (fun i j => raw10695step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10695step1 raw10695step0; decide +kernel
      have hl : raw10695step1Labels = raw10695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10695step0 raw10695step0Labels permutation56 hz
    mixedMoment B raw10695step1 raw10695step1Labels = mixedMoment B raw10695step2 raw10695step2Labels := by
      have ha : raw10695step2 = (fun i j => raw10695step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10695step2 raw10695step1; decide +kernel
      have hl : raw10695step2Labels = raw10695step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10695step1 raw10695step1Labels permutation8 permutation3
    mixedMoment B raw10695step2 raw10695step2Labels = mixedMoment B raw10695step3 raw10695step3Labels := by
      have ha : raw10695step3 = raw10695step2 := by apply Matrix.ext; unfold raw10695step3 raw10695step2; decide +kernel
      have hl : raw10695step2Labels = labelEmbedding6 ∘ raw10695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10695step2 raw10695step2Labels raw10695step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5023 node5023Labels := by rfl

def raw10696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw10696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw10696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw10696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10696step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10696step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10696step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10696 raw10696Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw10696 raw10696Labels = mixedMoment B raw10696step0 raw10696step0Labels := by
      have hz : ∀ j, raw10696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10696step0 = (fun i j => raw10696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10696step0 raw10696; decide +kernel
      have hl : raw10696step0Labels = raw10696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10696 raw10696Labels permutation346 hz
    mixedMoment B raw10696step0 raw10696step0Labels = mixedMoment B raw10696step1 raw10696step1Labels := by
      have hz : ∀ j, raw10696step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10696step1 = (fun i j => raw10696step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10696step1 raw10696step0; decide +kernel
      have hl : raw10696step1Labels = raw10696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10696step0 raw10696step0Labels permutation56 hz
    mixedMoment B raw10696step1 raw10696step1Labels = mixedMoment B raw10696step2 raw10696step2Labels := by
      have ha : raw10696step2 = (fun i j => raw10696step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10696step2 raw10696step1; decide +kernel
      have hl : raw10696step2Labels = raw10696step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10696step1 raw10696step1Labels permutation9 permutation3
    mixedMoment B raw10696step2 raw10696step2Labels = mixedMoment B raw10696step3 raw10696step3Labels := by
      have ha : raw10696step3 = raw10696step2 := by apply Matrix.ext; unfold raw10696step3 raw10696step2; decide +kernel
      have hl : raw10696step2Labels = labelEmbedding6 ∘ raw10696step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10696step2 raw10696step2Labels raw10696step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw10697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw10697step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw10697step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10697 raw10697Labels = mixedMoment B node4421 node4421Labels := by
  calc
    mixedMoment B raw10697 raw10697Labels = mixedMoment B raw10697step0 raw10697step0Labels := by
      have hz : ∀ j, raw10697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10697step0 = (fun i j => raw10697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10697step0 raw10697; decide +kernel
      have hl : raw10697step0Labels = raw10697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10697 raw10697Labels permutation346 hz
    mixedMoment B raw10697step0 raw10697step0Labels = mixedMoment B raw10697step1 raw10697step1Labels := by
      have hz : ∀ j, raw10697step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10697step1 = (fun i j => raw10697step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10697step1 raw10697step0; decide +kernel
      have hl : raw10697step1Labels = raw10697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10697step0 raw10697step0Labels permutation56 hz
    mixedMoment B raw10697step1 raw10697step1Labels = mixedMoment B raw10697step2 raw10697step2Labels := by
      have ha : raw10697step2 = (fun i j => raw10697step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10697step2 raw10697step1; decide +kernel
      have hl : raw10697step2Labels = raw10697step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10697step1 raw10697step1Labels permutation8 permutation3
    mixedMoment B raw10697step2 raw10697step2Labels = mixedMoment B raw10697step3 raw10697step3Labels := by
      have ha : raw10697step3 = raw10697step2 := by apply Matrix.ext; unfold raw10697step3 raw10697step2; decide +kernel
      have hl : raw10697step2Labels = labelEmbedding6 ∘ raw10697step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10697step2 raw10697step2Labels raw10697step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4421 node4421Labels := by rfl

def raw10698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10698step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10698 raw10698Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw10698 raw10698Labels = mixedMoment B raw10698step0 raw10698step0Labels := by
      have hz : ∀ j, raw10698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10698step0 = (fun i j => raw10698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10698step0 raw10698; decide +kernel
      have hl : raw10698step0Labels = raw10698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10698 raw10698Labels permutation346 hz
    mixedMoment B raw10698step0 raw10698step0Labels = mixedMoment B raw10698step1 raw10698step1Labels := by
      have ha : raw10698step1 = (fun i j => raw10698step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10698step1 raw10698step0; decide +kernel
      have hl : raw10698step1Labels = raw10698step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10698step0 raw10698step0Labels permutation151 permutation5
    mixedMoment B raw10698step1 raw10698step1Labels = mixedMoment B raw10698step2 raw10698step2Labels := by
      have ha : raw10698step2 = raw10698step1 := by apply Matrix.ext; unfold raw10698step2 raw10698step1; decide +kernel
      have hl : raw10698step1Labels = labelEmbedding8 ∘ raw10698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10698step1 raw10698step1Labels raw10698step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw10699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10699step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10699 raw10699Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw10699 raw10699Labels = mixedMoment B raw10699step0 raw10699step0Labels := by
      have hz : ∀ j, raw10699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10699step0 = (fun i j => raw10699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10699step0 raw10699; decide +kernel
      have hl : raw10699step0Labels = raw10699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10699 raw10699Labels permutation265 hz
    mixedMoment B raw10699step0 raw10699step0Labels = mixedMoment B raw10699step1 raw10699step1Labels := by
      have ha : raw10699step1 = (fun i j => raw10699step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10699step1 raw10699step0; decide +kernel
      have hl : raw10699step1Labels = raw10699step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10699step0 raw10699step0Labels permutation151 permutation5
    mixedMoment B raw10699step1 raw10699step1Labels = mixedMoment B raw10699step2 raw10699step2Labels := by
      have ha : raw10699step2 = raw10699step1 := by apply Matrix.ext; unfold raw10699step2 raw10699step1; decide +kernel
      have hl : raw10699step1Labels = labelEmbedding8 ∘ raw10699step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10699step1 raw10699step1Labels raw10699step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw10700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw10700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10700step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10700step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10700step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10700 raw10700Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw10700 raw10700Labels = mixedMoment B raw10700step0 raw10700step0Labels := by
      have hz : ∀ j, raw10700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10700step0 = (fun i j => raw10700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10700step0 raw10700; decide +kernel
      have hl : raw10700step0Labels = raw10700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10700 raw10700Labels permutation346 hz
    mixedMoment B raw10700step0 raw10700step0Labels = mixedMoment B raw10700step1 raw10700step1Labels := by
      have hz : ∀ j, raw10700step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10700step1 = (fun i j => raw10700step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10700step1 raw10700step0; decide +kernel
      have hl : raw10700step1Labels = raw10700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10700step0 raw10700step0Labels permutation56 hz
    mixedMoment B raw10700step1 raw10700step1Labels = mixedMoment B raw10700step2 raw10700step2Labels := by
      have ha : raw10700step2 = (fun i j => raw10700step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10700step2 raw10700step1; decide +kernel
      have hl : raw10700step2Labels = raw10700step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10700step1 raw10700step1Labels permutation31 permutation5
    mixedMoment B raw10700step2 raw10700step2Labels = mixedMoment B raw10700step3 raw10700step3Labels := by
      have ha : raw10700step3 = raw10700step2 := by apply Matrix.ext; unfold raw10700step3 raw10700step2; decide +kernel
      have hl : raw10700step2Labels = labelEmbedding8 ∘ raw10700step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10700step2 raw10700step2Labels raw10700step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw10701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw10701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw10701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw10701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10701step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10701step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10701step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10701 raw10701Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw10701 raw10701Labels = mixedMoment B raw10701step0 raw10701step0Labels := by
      have hz : ∀ j, raw10701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10701step0 = (fun i j => raw10701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10701step0 raw10701; decide +kernel
      have hl : raw10701step0Labels = raw10701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10701 raw10701Labels permutation346 hz
    mixedMoment B raw10701step0 raw10701step0Labels = mixedMoment B raw10701step1 raw10701step1Labels := by
      have hz : ∀ j, raw10701step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10701step1 = (fun i j => raw10701step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10701step1 raw10701step0; decide +kernel
      have hl : raw10701step1Labels = raw10701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10701step0 raw10701step0Labels permutation56 hz
    mixedMoment B raw10701step1 raw10701step1Labels = mixedMoment B raw10701step2 raw10701step2Labels := by
      have ha : raw10701step2 = (fun i j => raw10701step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10701step2 raw10701step1; decide +kernel
      have hl : raw10701step2Labels = raw10701step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10701step1 raw10701step1Labels permutation29 permutation5
    mixedMoment B raw10701step2 raw10701step2Labels = mixedMoment B raw10701step3 raw10701step3Labels := by
      have ha : raw10701step3 = raw10701step2 := by apply Matrix.ext; unfold raw10701step3 raw10701step2; decide +kernel
      have hl : raw10701step2Labels = labelEmbedding8 ∘ raw10701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10701step2 raw10701step2Labels raw10701step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw10702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw10702step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw10702step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10702step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw10702step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10702 raw10702Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw10702 raw10702Labels = mixedMoment B raw10702step0 raw10702step0Labels := by
      have hz : ∀ j, raw10702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10702step0 = (fun i j => raw10702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10702step0 raw10702; decide +kernel
      have hl : raw10702step0Labels = raw10702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10702 raw10702Labels permutation434 hz
    mixedMoment B raw10702step0 raw10702step0Labels = mixedMoment B raw10702step1 raw10702step1Labels := by
      have hz : ∀ j, raw10702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10702step1 = (fun i j => raw10702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10702step1 raw10702step0; decide +kernel
      have hl : raw10702step1Labels = raw10702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10702step0 raw10702step0Labels permutation80 hz
    mixedMoment B raw10702step1 raw10702step1Labels = mixedMoment B raw10702step2 raw10702step2Labels := by
      have ha : raw10702step2 = (fun i j => raw10702step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10702step2 raw10702step1; decide +kernel
      have hl : raw10702step2Labels = raw10702step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10702step1 raw10702step1Labels permutation16 permutation4
    mixedMoment B raw10702step2 raw10702step2Labels = mixedMoment B raw10702step3 raw10702step3Labels := by
      have ha : raw10702step3 = -raw10702step2 := by apply Matrix.ext; change ∀ i j, raw10702step3 i j = -(raw10702step2 i j); unfold raw10702step3 raw10702step2; decide +kernel
      have hl : raw10702step3Labels = raw10702step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10702step3 raw10702step3Labels = mixedMoment B raw10702step4 raw10702step4Labels := by
      have ha : raw10702step4 = raw10702step3 := by apply Matrix.ext; unfold raw10702step4 raw10702step3; decide +kernel
      have hl : raw10702step3Labels = labelEmbedding7 ∘ raw10702step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10702step3 raw10702step3Labels raw10702step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw10703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10703step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10703step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10703step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10703 raw10703Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw10703 raw10703Labels = mixedMoment B raw10703step0 raw10703step0Labels := by
      have hz : ∀ j, raw10703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10703step0 = (fun i j => raw10703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10703step0 raw10703; decide +kernel
      have hl : raw10703step0Labels = raw10703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10703 raw10703Labels permutation434 hz
    mixedMoment B raw10703step0 raw10703step0Labels = mixedMoment B raw10703step1 raw10703step1Labels := by
      have ha : raw10703step1 = (fun i j => raw10703step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10703step1 raw10703step0; decide +kernel
      have hl : raw10703step1Labels = raw10703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10703step0 raw10703step0Labels permutation43 permutation7
    mixedMoment B raw10703step1 raw10703step1Labels = mixedMoment B raw10703step2 raw10703step2Labels := by
      have ha : raw10703step2 = -raw10703step1 := by apply Matrix.ext; change ∀ i j, raw10703step2 i j = -(raw10703step1 i j); unfold raw10703step2 raw10703step1; decide +kernel
      have hl : raw10703step2Labels = raw10703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10703step2 raw10703step2Labels = mixedMoment B raw10703step3 raw10703step3Labels := by
      have ha : raw10703step3 = raw10703step2 := by apply Matrix.ext; unfold raw10703step3 raw10703step2; decide +kernel
      have hl : raw10703step2Labels = labelEmbedding10 ∘ raw10703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10703step2 raw10703step2Labels raw10703step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw10704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10704step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10704step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10704step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10704step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10704 raw10704Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw10704 raw10704Labels = mixedMoment B raw10704step0 raw10704step0Labels := by
      have hz : ∀ j, raw10704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10704step0 = (fun i j => raw10704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10704step0 raw10704; decide +kernel
      have hl : raw10704step0Labels = raw10704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10704 raw10704Labels permutation346 hz
    mixedMoment B raw10704step0 raw10704step0Labels = mixedMoment B raw10704step1 raw10704step1Labels := by
      have ha : raw10704step1 = (fun i j => raw10704step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10704step1 raw10704step0; decide +kernel
      have hl : raw10704step1Labels = raw10704step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10704step0 raw10704step0Labels permutation43 permutation7
    mixedMoment B raw10704step1 raw10704step1Labels = mixedMoment B raw10704step2 raw10704step2Labels := by
      have ha : raw10704step2 = -raw10704step1 := by apply Matrix.ext; change ∀ i j, raw10704step2 i j = -(raw10704step1 i j); unfold raw10704step2 raw10704step1; decide +kernel
      have hl : raw10704step2Labels = raw10704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10704step2 raw10704step2Labels = mixedMoment B raw10704step3 raw10704step3Labels := by
      have ha : raw10704step3 = raw10704step2 := by apply Matrix.ext; unfold raw10704step3 raw10704step2; decide +kernel
      have hl : raw10704step2Labels = labelEmbedding10 ∘ raw10704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10704step2 raw10704step2Labels raw10704step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw10705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw10705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw10705step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10705step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10705step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10705step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10705 raw10705Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw10705 raw10705Labels = mixedMoment B raw10705step0 raw10705step0Labels := by
      have hz : ∀ j, raw10705 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10705step0 = (fun i j => raw10705 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10705step0 raw10705; decide +kernel
      have hl : raw10705step0Labels = raw10705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10705 raw10705Labels permutation434 hz
    mixedMoment B raw10705step0 raw10705step0Labels = mixedMoment B raw10705step1 raw10705step1Labels := by
      have hz : ∀ j, raw10705step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10705step1 = (fun i j => raw10705step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10705step1 raw10705step0; decide +kernel
      have hl : raw10705step1Labels = raw10705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10705step0 raw10705step0Labels permutation80 hz
    mixedMoment B raw10705step1 raw10705step1Labels = mixedMoment B raw10705step2 raw10705step2Labels := by
      have ha : raw10705step2 = (fun i j => raw10705step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10705step2 raw10705step1; decide +kernel
      have hl : raw10705step2Labels = raw10705step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10705step1 raw10705step1Labels permutation13 permutation7
    mixedMoment B raw10705step2 raw10705step2Labels = mixedMoment B raw10705step3 raw10705step3Labels := by
      have ha : raw10705step3 = -raw10705step2 := by apply Matrix.ext; change ∀ i j, raw10705step3 i j = -(raw10705step2 i j); unfold raw10705step3 raw10705step2; decide +kernel
      have hl : raw10705step3Labels = raw10705step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10705step3 raw10705step3Labels = mixedMoment B raw10705step4 raw10705step4Labels := by
      have ha : raw10705step4 = raw10705step3 := by apply Matrix.ext; unfold raw10705step4 raw10705step3; decide +kernel
      have hl : raw10705step3Labels = labelEmbedding10 ∘ raw10705step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10705step3 raw10705step3Labels raw10705step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw10706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw10706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10706step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10706step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10706step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10706step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10706 raw10706Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw10706 raw10706Labels = mixedMoment B raw10706step0 raw10706step0Labels := by
      have hz : ∀ j, raw10706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10706step0 = (fun i j => raw10706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10706step0 raw10706; decide +kernel
      have hl : raw10706step0Labels = raw10706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10706 raw10706Labels permutation434 hz
    mixedMoment B raw10706step0 raw10706step0Labels = mixedMoment B raw10706step1 raw10706step1Labels := by
      have hz : ∀ j, raw10706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10706step1 = (fun i j => raw10706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10706step1 raw10706step0; decide +kernel
      have hl : raw10706step1Labels = raw10706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10706step0 raw10706step0Labels permutation80 hz
    mixedMoment B raw10706step1 raw10706step1Labels = mixedMoment B raw10706step2 raw10706step2Labels := by
      have ha : raw10706step2 = (fun i j => raw10706step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10706step2 raw10706step1; decide +kernel
      have hl : raw10706step2Labels = raw10706step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10706step1 raw10706step1Labels permutation13 permutation7
    mixedMoment B raw10706step2 raw10706step2Labels = mixedMoment B raw10706step3 raw10706step3Labels := by
      have ha : raw10706step3 = -raw10706step2 := by apply Matrix.ext; change ∀ i j, raw10706step3 i j = -(raw10706step2 i j); unfold raw10706step3 raw10706step2; decide +kernel
      have hl : raw10706step3Labels = raw10706step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10706step3 raw10706step3Labels = mixedMoment B raw10706step4 raw10706step4Labels := by
      have ha : raw10706step4 = raw10706step3 := by apply Matrix.ext; unfold raw10706step4 raw10706step3; decide +kernel
      have hl : raw10706step3Labels = labelEmbedding10 ∘ raw10706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10706step3 raw10706step3Labels raw10706step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw10707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10707 raw10707Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw10707 raw10707Labels = mixedMoment B raw10707step0 raw10707step0Labels := by
      have hz : ∀ j, raw10707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10707step0 = (fun i j => raw10707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10707step0 raw10707; decide +kernel
      have hl : raw10707step0Labels = raw10707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10707 raw10707Labels permutation434 hz
    mixedMoment B raw10707step0 raw10707step0Labels = mixedMoment B raw10707step1 raw10707step1Labels := by
      have hz : ∀ j, raw10707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10707step1 = (fun i j => raw10707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10707step1 raw10707step0; decide +kernel
      have hl : raw10707step1Labels = raw10707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10707step0 raw10707step0Labels permutation80 hz
    mixedMoment B raw10707step1 raw10707step1Labels = mixedMoment B raw10707step2 raw10707step2Labels := by
      have ha : raw10707step2 = (fun i j => raw10707step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10707step2 raw10707step1; decide +kernel
      have hl : raw10707step2Labels = raw10707step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10707step1 raw10707step1Labels permutation10 permutation2
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw10708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10708 raw10708Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw10708 raw10708Labels = mixedMoment B raw10708step0 raw10708step0Labels := by
      have hz : ∀ j, raw10708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10708step0 = (fun i j => raw10708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10708step0 raw10708; decide +kernel
      have hl : raw10708step0Labels = raw10708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10708 raw10708Labels permutation434 hz
    mixedMoment B raw10708step0 raw10708step0Labels = mixedMoment B raw10708step1 raw10708step1Labels := by
      have ha : raw10708step1 = (fun i j => raw10708step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10708step1 raw10708step0; decide +kernel
      have hl : raw10708step1Labels = raw10708step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10708step0 raw10708step0Labels permutation40 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw10709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10709 raw10709Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw10709 raw10709Labels = mixedMoment B raw10709step0 raw10709step0Labels := by
      have hz : ∀ j, raw10709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10709step0 = (fun i j => raw10709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10709step0 raw10709; decide +kernel
      have hl : raw10709step0Labels = raw10709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10709 raw10709Labels permutation346 hz
    mixedMoment B raw10709step0 raw10709step0Labels = mixedMoment B raw10709step1 raw10709step1Labels := by
      have ha : raw10709step1 = (fun i j => raw10709step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10709step1 raw10709step0; decide +kernel
      have hl : raw10709step1Labels = raw10709step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10709step0 raw10709step0Labels permutation40 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw10710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw10710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10710 raw10710Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw10710 raw10710Labels = mixedMoment B raw10710step0 raw10710step0Labels := by
      have hz : ∀ j, raw10710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10710step0 = (fun i j => raw10710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10710step0 raw10710; decide +kernel
      have hl : raw10710step0Labels = raw10710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10710 raw10710Labels permutation434 hz
    mixedMoment B raw10710step0 raw10710step0Labels = mixedMoment B raw10710step1 raw10710step1Labels := by
      have hz : ∀ j, raw10710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10710step1 = (fun i j => raw10710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10710step1 raw10710step0; decide +kernel
      have hl : raw10710step1Labels = raw10710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10710step0 raw10710step0Labels permutation80 hz
    mixedMoment B raw10710step1 raw10710step1Labels = mixedMoment B raw10710step2 raw10710step2Labels := by
      have ha : raw10710step2 = (fun i j => raw10710step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10710step2 raw10710step1; decide +kernel
      have hl : raw10710step2Labels = raw10710step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10710step1 raw10710step1Labels permutation10 permutation2
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw10711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw10711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10711step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10711step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10711step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10711step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10711 raw10711Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw10711 raw10711Labels = mixedMoment B raw10711step0 raw10711step0Labels := by
      have hz : ∀ j, raw10711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10711step0 = (fun i j => raw10711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10711step0 raw10711; decide +kernel
      have hl : raw10711step0Labels = raw10711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10711 raw10711Labels permutation434 hz
    mixedMoment B raw10711step0 raw10711step0Labels = mixedMoment B raw10711step1 raw10711step1Labels := by
      have hz : ∀ j, raw10711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10711step1 = (fun i j => raw10711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10711step1 raw10711step0; decide +kernel
      have hl : raw10711step1Labels = raw10711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10711step0 raw10711step0Labels permutation80 hz
    mixedMoment B raw10711step1 raw10711step1Labels = mixedMoment B raw10711step2 raw10711step2Labels := by
      have ha : raw10711step2 = (fun i j => raw10711step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10711step2 raw10711step1; decide +kernel
      have hl : raw10711step2Labels = raw10711step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10711step1 raw10711step1Labels permutation13 permutation7
    mixedMoment B raw10711step2 raw10711step2Labels = mixedMoment B raw10711step3 raw10711step3Labels := by
      have ha : raw10711step3 = -raw10711step2 := by apply Matrix.ext; change ∀ i j, raw10711step3 i j = -(raw10711step2 i j); unfold raw10711step3 raw10711step2; decide +kernel
      have hl : raw10711step3Labels = raw10711step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10711step3 raw10711step3Labels = mixedMoment B raw10711step4 raw10711step4Labels := by
      have ha : raw10711step4 = raw10711step3 := by apply Matrix.ext; unfold raw10711step4 raw10711step3; decide +kernel
      have hl : raw10711step3Labels = labelEmbedding10 ∘ raw10711step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10711step3 raw10711step3Labels raw10711step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw10712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10712 raw10712Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw10712 raw10712Labels = mixedMoment B raw10712step0 raw10712step0Labels := by
      have hz : ∀ j, raw10712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10712step0 = (fun i j => raw10712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10712step0 raw10712; decide +kernel
      have hl : raw10712step0Labels = raw10712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10712 raw10712Labels permutation434 hz
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw10713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10713 raw10713Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw10713 raw10713Labels = mixedMoment B raw10713step0 raw10713step0Labels := by
      have hz : ∀ j, raw10713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10713step0 = (fun i j => raw10713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10713step0 raw10713; decide +kernel
      have hl : raw10713step0Labels = raw10713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10713 raw10713Labels permutation434 hz
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw10714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10714 raw10714Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw10714 raw10714Labels = mixedMoment B raw10714step0 raw10714step0Labels := by
      have ha : raw10714step0 = (fun i j => raw10714 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10714step0 raw10714; decide +kernel
      have hl : raw10714step0Labels = raw10714Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10714 raw10714Labels permutation200 permutation2
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw10715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10715 raw10715Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw10715 raw10715Labels = mixedMoment B raw10715step0 raw10715step0Labels := by
      have hz : ∀ j, raw10715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10715step0 = (fun i j => raw10715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10715step0 raw10715; decide +kernel
      have hl : raw10715step0Labels = raw10715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10715 raw10715Labels permutation434 hz
    mixedMoment B raw10715step0 raw10715step0Labels = mixedMoment B raw10715step1 raw10715step1Labels := by
      have ha : raw10715step1 = (fun i j => raw10715step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10715step1 raw10715step0; decide +kernel
      have hl : raw10715step1Labels = raw10715step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10715step0 raw10715step0Labels permutation44 permutation2
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw10716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10716step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10716step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10716step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10716 raw10716Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw10716 raw10716Labels = mixedMoment B raw10716step0 raw10716step0Labels := by
      have hz : ∀ j, raw10716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10716step0 = (fun i j => raw10716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10716step0 raw10716; decide +kernel
      have hl : raw10716step0Labels = raw10716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10716 raw10716Labels permutation434 hz
    mixedMoment B raw10716step0 raw10716step0Labels = mixedMoment B raw10716step1 raw10716step1Labels := by
      have ha : raw10716step1 = (fun i j => raw10716step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10716step1 raw10716step0; decide +kernel
      have hl : raw10716step1Labels = raw10716step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10716step0 raw10716step0Labels permutation43 permutation7
    mixedMoment B raw10716step1 raw10716step1Labels = mixedMoment B raw10716step2 raw10716step2Labels := by
      have ha : raw10716step2 = -raw10716step1 := by apply Matrix.ext; change ∀ i j, raw10716step2 i j = -(raw10716step1 i j); unfold raw10716step2 raw10716step1; decide +kernel
      have hl : raw10716step2Labels = raw10716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10716step2 raw10716step2Labels = mixedMoment B raw10716step3 raw10716step3Labels := by
      have ha : raw10716step3 = raw10716step2 := by apply Matrix.ext; unfold raw10716step3 raw10716step2; decide +kernel
      have hl : raw10716step2Labels = labelEmbedding10 ∘ raw10716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10716step2 raw10716step2Labels raw10716step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw10717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10717 raw10717Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw10717 raw10717Labels = mixedMoment B raw10717step0 raw10717step0Labels := by
      have hz : ∀ j, raw10717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10717step0 = (fun i j => raw10717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10717step0 raw10717; decide +kernel
      have hl : raw10717step0Labels = raw10717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10717 raw10717Labels permutation346 hz
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw10718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10718 raw10718Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw10718 raw10718Labels = mixedMoment B raw10718step0 raw10718step0Labels := by
      have hz : ∀ j, raw10718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10718step0 = (fun i j => raw10718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10718step0 raw10718; decide +kernel
      have hl : raw10718step0Labels = raw10718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10718 raw10718Labels permutation346 hz
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw10719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10719 raw10719Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw10719 raw10719Labels = mixedMoment B raw10719step0 raw10719step0Labels := by
      have ha : raw10719step0 = (fun i j => raw10719 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10719step0 raw10719; decide +kernel
      have hl : raw10719step0Labels = raw10719Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10719 raw10719Labels permutation176 permutation2
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw10720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10720 raw10720Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw10720 raw10720Labels = mixedMoment B raw10720step0 raw10720step0Labels := by
      have hz : ∀ j, raw10720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10720step0 = (fun i j => raw10720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10720step0 raw10720; decide +kernel
      have hl : raw10720step0Labels = raw10720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10720 raw10720Labels permutation346 hz
    mixedMoment B raw10720step0 raw10720step0Labels = mixedMoment B raw10720step1 raw10720step1Labels := by
      have ha : raw10720step1 = (fun i j => raw10720step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10720step1 raw10720step0; decide +kernel
      have hl : raw10720step1Labels = raw10720step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10720step0 raw10720step0Labels permutation44 permutation2
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw10721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10721step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10721step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10721step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10721step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10721 raw10721Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw10721 raw10721Labels = mixedMoment B raw10721step0 raw10721step0Labels := by
      have hz : ∀ j, raw10721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10721step0 = (fun i j => raw10721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10721step0 raw10721; decide +kernel
      have hl : raw10721step0Labels = raw10721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10721 raw10721Labels permutation346 hz
    mixedMoment B raw10721step0 raw10721step0Labels = mixedMoment B raw10721step1 raw10721step1Labels := by
      have ha : raw10721step1 = (fun i j => raw10721step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10721step1 raw10721step0; decide +kernel
      have hl : raw10721step1Labels = raw10721step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10721step0 raw10721step0Labels permutation43 permutation7
    mixedMoment B raw10721step1 raw10721step1Labels = mixedMoment B raw10721step2 raw10721step2Labels := by
      have ha : raw10721step2 = -raw10721step1 := by apply Matrix.ext; change ∀ i j, raw10721step2 i j = -(raw10721step1 i j); unfold raw10721step2 raw10721step1; decide +kernel
      have hl : raw10721step2Labels = raw10721step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10721step2 raw10721step2Labels = mixedMoment B raw10721step3 raw10721step3Labels := by
      have ha : raw10721step3 = raw10721step2 := by apply Matrix.ext; unfold raw10721step3 raw10721step2; decide +kernel
      have hl : raw10721step2Labels = labelEmbedding10 ∘ raw10721step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10721step2 raw10721step2Labels raw10721step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw10722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw10722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10722step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10722 raw10722Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw10722 raw10722Labels = mixedMoment B raw10722step0 raw10722step0Labels := by
      have hz : ∀ j, raw10722 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10722step0 = (fun i j => raw10722 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10722step0 raw10722; decide +kernel
      have hl : raw10722step0Labels = raw10722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10722 raw10722Labels permutation434 hz
    mixedMoment B raw10722step0 raw10722step0Labels = mixedMoment B raw10722step1 raw10722step1Labels := by
      have hz : ∀ j, raw10722step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10722step1 = (fun i j => raw10722step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10722step1 raw10722step0; decide +kernel
      have hl : raw10722step1Labels = raw10722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10722step0 raw10722step0Labels permutation80 hz
    mixedMoment B raw10722step1 raw10722step1Labels = mixedMoment B raw10722step2 raw10722step2Labels := by
      have ha : raw10722step2 = (fun i j => raw10722step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10722step2 raw10722step1; decide +kernel
      have hl : raw10722step2Labels = raw10722step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10722step1 raw10722step1Labels permutation9 permutation2
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw10723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw10723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10723 raw10723Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw10723 raw10723Labels = mixedMoment B raw10723step0 raw10723step0Labels := by
      have hz : ∀ j, raw10723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10723step0 = (fun i j => raw10723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10723step0 raw10723; decide +kernel
      have hl : raw10723step0Labels = raw10723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10723 raw10723Labels permutation434 hz
    mixedMoment B raw10723step0 raw10723step0Labels = mixedMoment B raw10723step1 raw10723step1Labels := by
      have hz : ∀ j, raw10723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10723step1 = (fun i j => raw10723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10723step1 raw10723step0; decide +kernel
      have hl : raw10723step1Labels = raw10723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10723step0 raw10723step0Labels permutation80 hz
    mixedMoment B raw10723step1 raw10723step1Labels = mixedMoment B raw10723step2 raw10723step2Labels := by
      have ha : raw10723step2 = (fun i j => raw10723step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10723step2 raw10723step1; decide +kernel
      have hl : raw10723step2Labels = raw10723step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10723step1 raw10723step1Labels permutation9 permutation2
    _ = mixedMoment B node4884 node4884Labels := by rfl

def raw10724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10724 raw10724Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw10724 raw10724Labels = mixedMoment B raw10724step0 raw10724step0Labels := by
      have hz : ∀ j, raw10724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10724step0 = (fun i j => raw10724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10724step0 raw10724; decide +kernel
      have hl : raw10724step0Labels = raw10724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10724 raw10724Labels permutation434 hz
    mixedMoment B raw10724step0 raw10724step0Labels = mixedMoment B raw10724step1 raw10724step1Labels := by
      have ha : raw10724step1 = (fun i j => raw10724step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10724step1 raw10724step0; decide +kernel
      have hl : raw10724step1Labels = raw10724step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10724step0 raw10724step0Labels permutation39 permutation2
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw10725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10725 raw10725Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw10725 raw10725Labels = mixedMoment B raw10725step0 raw10725step0Labels := by
      have hz : ∀ j, raw10725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10725step0 = (fun i j => raw10725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10725step0 raw10725; decide +kernel
      have hl : raw10725step0Labels = raw10725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10725 raw10725Labels permutation346 hz
    mixedMoment B raw10725step0 raw10725step0Labels = mixedMoment B raw10725step1 raw10725step1Labels := by
      have ha : raw10725step1 = (fun i j => raw10725step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10725step1 raw10725step0; decide +kernel
      have hl : raw10725step1Labels = raw10725step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10725step0 raw10725step0Labels permutation39 permutation2
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw10726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw10726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw10726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw10726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10726step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10726step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10726step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10726step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10726 raw10726Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw10726 raw10726Labels = mixedMoment B raw10726step0 raw10726step0Labels := by
      have hz : ∀ j, raw10726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10726step0 = (fun i j => raw10726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10726step0 raw10726; decide +kernel
      have hl : raw10726step0Labels = raw10726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10726 raw10726Labels permutation434 hz
    mixedMoment B raw10726step0 raw10726step0Labels = mixedMoment B raw10726step1 raw10726step1Labels := by
      have hz : ∀ j, raw10726step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10726step1 = (fun i j => raw10726step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10726step1 raw10726step0; decide +kernel
      have hl : raw10726step1Labels = raw10726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10726step0 raw10726step0Labels permutation80 hz
    mixedMoment B raw10726step1 raw10726step1Labels = mixedMoment B raw10726step2 raw10726step2Labels := by
      have ha : raw10726step2 = (fun i j => raw10726step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10726step2 raw10726step1; decide +kernel
      have hl : raw10726step2Labels = raw10726step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10726step1 raw10726step1Labels permutation13 permutation7
    mixedMoment B raw10726step2 raw10726step2Labels = mixedMoment B raw10726step3 raw10726step3Labels := by
      have ha : raw10726step3 = -raw10726step2 := by apply Matrix.ext; change ∀ i j, raw10726step3 i j = -(raw10726step2 i j); unfold raw10726step3 raw10726step2; decide +kernel
      have hl : raw10726step3Labels = raw10726step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10726step3 raw10726step3Labels = mixedMoment B raw10726step4 raw10726step4Labels := by
      have ha : raw10726step4 = raw10726step3 := by apply Matrix.ext; unfold raw10726step4 raw10726step3; decide +kernel
      have hl : raw10726step3Labels = labelEmbedding10 ∘ raw10726step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10726step3 raw10726step3Labels raw10726step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw10727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10727 raw10727Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw10727 raw10727Labels = mixedMoment B raw10727step0 raw10727step0Labels := by
      have hz : ∀ j, raw10727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10727step0 = (fun i j => raw10727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10727step0 raw10727; decide +kernel
      have hl : raw10727step0Labels = raw10727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10727 raw10727Labels permutation434 hz
    mixedMoment B raw10727step0 raw10727step0Labels = mixedMoment B raw10727step1 raw10727step1Labels := by
      have hz : ∀ j, raw10727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10727step1 = (fun i j => raw10727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10727step1 raw10727step0; decide +kernel
      have hl : raw10727step1Labels = raw10727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10727step0 raw10727step0Labels permutation80 hz
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw10728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10728step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw10728step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw10728step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw10728step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10728 raw10728Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw10728 raw10728Labels = mixedMoment B raw10728step0 raw10728step0Labels := by
      have hz : ∀ j, raw10728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10728step0 = (fun i j => raw10728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10728step0 raw10728; decide +kernel
      have hl : raw10728step0Labels = raw10728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10728 raw10728Labels permutation434 hz
    mixedMoment B raw10728step0 raw10728step0Labels = mixedMoment B raw10728step1 raw10728step1Labels := by
      have hz : ∀ j, raw10728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10728step1 = (fun i j => raw10728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10728step1 raw10728step0; decide +kernel
      have hl : raw10728step1Labels = raw10728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10728step0 raw10728step0Labels permutation80 hz
    mixedMoment B raw10728step1 raw10728step1Labels = mixedMoment B raw10728step2 raw10728step2Labels := by
      have ha : raw10728step2 = (fun i j => raw10728step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10728step2 raw10728step1; decide +kernel
      have hl : raw10728step2Labels = raw10728step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10728step1 raw10728step1Labels permutation31 permutation3
    mixedMoment B raw10728step2 raw10728step2Labels = mixedMoment B raw10728step3 raw10728step3Labels := by
      have ha : raw10728step3 = -raw10728step2 := by apply Matrix.ext; change ∀ i j, raw10728step3 i j = -(raw10728step2 i j); unfold raw10728step3 raw10728step2; decide +kernel
      have hl : raw10728step3Labels = raw10728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10728step3 raw10728step3Labels = mixedMoment B raw10728step4 raw10728step4Labels := by
      have ha : raw10728step4 = raw10728step3 := by apply Matrix.ext; unfold raw10728step4 raw10728step3; decide +kernel
      have hl : raw10728step3Labels = labelEmbedding6 ∘ raw10728step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10728step3 raw10728step3Labels raw10728step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw10729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10729step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10729 raw10729Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw10729 raw10729Labels = mixedMoment B raw10729step0 raw10729step0Labels := by
      have hz : ∀ j, raw10729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10729step0 = (fun i j => raw10729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10729step0 raw10729; decide +kernel
      have hl : raw10729step0Labels = raw10729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10729 raw10729Labels permutation434 hz
    mixedMoment B raw10729step0 raw10729step0Labels = mixedMoment B raw10729step1 raw10729step1Labels := by
      have ha : raw10729step1 = (fun i j => raw10729step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10729step1 raw10729step0; decide +kernel
      have hl : raw10729step1Labels = raw10729step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10729step0 raw10729step0Labels permutation38 permutation2
    _ = mixedMoment B node4819 node4819Labels := by rfl

def raw10730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10730step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10730 raw10730Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw10730 raw10730Labels = mixedMoment B raw10730step0 raw10730step0Labels := by
      have hz : ∀ j, raw10730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10730step0 = (fun i j => raw10730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10730step0 raw10730; decide +kernel
      have hl : raw10730step0Labels = raw10730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10730 raw10730Labels permutation346 hz
    mixedMoment B raw10730step0 raw10730step0Labels = mixedMoment B raw10730step1 raw10730step1Labels := by
      have ha : raw10730step1 = (fun i j => raw10730step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10730step1 raw10730step0; decide +kernel
      have hl : raw10730step1Labels = raw10730step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10730step0 raw10730step0Labels permutation38 permutation2
    _ = mixedMoment B node4819 node4819Labels := by rfl

def raw10731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw10731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw10731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw10731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw10731step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10731 raw10731Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw10731 raw10731Labels = mixedMoment B raw10731step0 raw10731step0Labels := by
      have hz : ∀ j, raw10731 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10731step0 = (fun i j => raw10731 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10731step0 raw10731; decide +kernel
      have hl : raw10731step0Labels = raw10731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10731 raw10731Labels permutation434 hz
    mixedMoment B raw10731step0 raw10731step0Labels = mixedMoment B raw10731step1 raw10731step1Labels := by
      have hz : ∀ j, raw10731step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10731step1 = (fun i j => raw10731step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10731step1 raw10731step0; decide +kernel
      have hl : raw10731step1Labels = raw10731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10731step0 raw10731step0Labels permutation80 hz
    mixedMoment B raw10731step1 raw10731step1Labels = mixedMoment B raw10731step2 raw10731step2Labels := by
      have ha : raw10731step2 = (fun i j => raw10731step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10731step2 raw10731step1; decide +kernel
      have hl : raw10731step2Labels = raw10731step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10731step1 raw10731step1Labels permutation10 permutation2
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw10732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10732step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw10732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10732step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10732step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10732step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10732step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10732 raw10732Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw10732 raw10732Labels = mixedMoment B raw10732step0 raw10732step0Labels := by
      have hz : ∀ j, raw10732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10732step0 = (fun i j => raw10732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10732step0 raw10732; decide +kernel
      have hl : raw10732step0Labels = raw10732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10732 raw10732Labels permutation434 hz
    mixedMoment B raw10732step0 raw10732step0Labels = mixedMoment B raw10732step1 raw10732step1Labels := by
      have hz : ∀ j, raw10732step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10732step1 = (fun i j => raw10732step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10732step1 raw10732step0; decide +kernel
      have hl : raw10732step1Labels = raw10732step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10732step0 raw10732step0Labels permutation80 hz
    mixedMoment B raw10732step1 raw10732step1Labels = mixedMoment B raw10732step2 raw10732step2Labels := by
      have ha : raw10732step2 = (fun i j => raw10732step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10732step2 raw10732step1; decide +kernel
      have hl : raw10732step2Labels = raw10732step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10732step1 raw10732step1Labels permutation13 permutation7
    mixedMoment B raw10732step2 raw10732step2Labels = mixedMoment B raw10732step3 raw10732step3Labels := by
      have ha : raw10732step3 = -raw10732step2 := by apply Matrix.ext; change ∀ i j, raw10732step3 i j = -(raw10732step2 i j); unfold raw10732step3 raw10732step2; decide +kernel
      have hl : raw10732step3Labels = raw10732step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10732step3 raw10732step3Labels = mixedMoment B raw10732step4 raw10732step4Labels := by
      have ha : raw10732step4 = raw10732step3 := by apply Matrix.ext; unfold raw10732step4 raw10732step3; decide +kernel
      have hl : raw10732step3Labels = labelEmbedding1 ∘ raw10732step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10732step3 raw10732step3Labels raw10732step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw10733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10733step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10733 raw10733Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw10733 raw10733Labels = mixedMoment B raw10733step0 raw10733step0Labels := by
      have hz : ∀ j, raw10733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10733step0 = (fun i j => raw10733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10733step0 raw10733; decide +kernel
      have hl : raw10733step0Labels = raw10733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10733 raw10733Labels permutation434 hz
    mixedMoment B raw10733step0 raw10733step0Labels = mixedMoment B raw10733step1 raw10733step1Labels := by
      have ha : raw10733step1 = (fun i j => raw10733step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10733step1 raw10733step0; decide +kernel
      have hl : raw10733step1Labels = raw10733step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10733step0 raw10733step0Labels permutation43 permutation7
    mixedMoment B raw10733step1 raw10733step1Labels = mixedMoment B raw10733step2 raw10733step2Labels := by
      have ha : raw10733step2 = -raw10733step1 := by apply Matrix.ext; change ∀ i j, raw10733step2 i j = -(raw10733step1 i j); unfold raw10733step2 raw10733step1; decide +kernel
      have hl : raw10733step2Labels = raw10733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10733step2 raw10733step2Labels = mixedMoment B raw10733step3 raw10733step3Labels := by
      have ha : raw10733step3 = raw10733step2 := by apply Matrix.ext; unfold raw10733step3 raw10733step2; decide +kernel
      have hl : raw10733step2Labels = labelEmbedding1 ∘ raw10733step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10733step2 raw10733step2Labels raw10733step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw10734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10734 raw10734Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw10734 raw10734Labels = mixedMoment B raw10734step0 raw10734step0Labels := by
      have hz : ∀ j, raw10734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10734step0 = (fun i j => raw10734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10734step0 raw10734; decide +kernel
      have hl : raw10734step0Labels = raw10734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10734 raw10734Labels permutation346 hz
    mixedMoment B raw10734step0 raw10734step0Labels = mixedMoment B raw10734step1 raw10734step1Labels := by
      have ha : raw10734step1 = (fun i j => raw10734step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10734step1 raw10734step0; decide +kernel
      have hl : raw10734step1Labels = raw10734step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10734step0 raw10734step0Labels permutation43 permutation7
    mixedMoment B raw10734step1 raw10734step1Labels = mixedMoment B raw10734step2 raw10734step2Labels := by
      have ha : raw10734step2 = -raw10734step1 := by apply Matrix.ext; change ∀ i j, raw10734step2 i j = -(raw10734step1 i j); unfold raw10734step2 raw10734step1; decide +kernel
      have hl : raw10734step2Labels = raw10734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10734step2 raw10734step2Labels = mixedMoment B raw10734step3 raw10734step3Labels := by
      have ha : raw10734step3 = raw10734step2 := by apply Matrix.ext; unfold raw10734step3 raw10734step2; decide +kernel
      have hl : raw10734step2Labels = labelEmbedding1 ∘ raw10734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10734step2 raw10734step2Labels raw10734step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw10735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw10735step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw10735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10735step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10735step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10735step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10735step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10735 raw10735Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw10735 raw10735Labels = mixedMoment B raw10735step0 raw10735step0Labels := by
      have hz : ∀ j, raw10735 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10735step0 = (fun i j => raw10735 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10735step0 raw10735; decide +kernel
      have hl : raw10735step0Labels = raw10735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10735 raw10735Labels permutation434 hz
    mixedMoment B raw10735step0 raw10735step0Labels = mixedMoment B raw10735step1 raw10735step1Labels := by
      have hz : ∀ j, raw10735step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10735step1 = (fun i j => raw10735step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10735step1 raw10735step0; decide +kernel
      have hl : raw10735step1Labels = raw10735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10735step0 raw10735step0Labels permutation80 hz
    mixedMoment B raw10735step1 raw10735step1Labels = mixedMoment B raw10735step2 raw10735step2Labels := by
      have ha : raw10735step2 = (fun i j => raw10735step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10735step2 raw10735step1; decide +kernel
      have hl : raw10735step2Labels = raw10735step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10735step1 raw10735step1Labels permutation13 permutation7
    mixedMoment B raw10735step2 raw10735step2Labels = mixedMoment B raw10735step3 raw10735step3Labels := by
      have ha : raw10735step3 = -raw10735step2 := by apply Matrix.ext; change ∀ i j, raw10735step3 i j = -(raw10735step2 i j); unfold raw10735step3 raw10735step2; decide +kernel
      have hl : raw10735step3Labels = raw10735step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10735step3 raw10735step3Labels = mixedMoment B raw10735step4 raw10735step4Labels := by
      have ha : raw10735step4 = raw10735step3 := by apply Matrix.ext; unfold raw10735step4 raw10735step3; decide +kernel
      have hl : raw10735step3Labels = labelEmbedding1 ∘ raw10735step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10735step3 raw10735step3Labels raw10735step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw10736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw10736step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10736step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10736step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10736step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10736 raw10736Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw10736 raw10736Labels = mixedMoment B raw10736step0 raw10736step0Labels := by
      have hz : ∀ j, raw10736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10736step0 = (fun i j => raw10736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10736step0 raw10736; decide +kernel
      have hl : raw10736step0Labels = raw10736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10736 raw10736Labels permutation434 hz
    mixedMoment B raw10736step0 raw10736step0Labels = mixedMoment B raw10736step1 raw10736step1Labels := by
      have hz : ∀ j, raw10736step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10736step1 = (fun i j => raw10736step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10736step1 raw10736step0; decide +kernel
      have hl : raw10736step1Labels = raw10736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10736step0 raw10736step0Labels permutation80 hz
    mixedMoment B raw10736step1 raw10736step1Labels = mixedMoment B raw10736step2 raw10736step2Labels := by
      have ha : raw10736step2 = (fun i j => raw10736step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10736step2 raw10736step1; decide +kernel
      have hl : raw10736step2Labels = raw10736step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10736step1 raw10736step1Labels permutation13 permutation7
    mixedMoment B raw10736step2 raw10736step2Labels = mixedMoment B raw10736step3 raw10736step3Labels := by
      have ha : raw10736step3 = -raw10736step2 := by apply Matrix.ext; change ∀ i j, raw10736step3 i j = -(raw10736step2 i j); unfold raw10736step3 raw10736step2; decide +kernel
      have hl : raw10736step3Labels = raw10736step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10736step3 raw10736step3Labels = mixedMoment B raw10736step4 raw10736step4Labels := by
      have ha : raw10736step4 = raw10736step3 := by apply Matrix.ext; unfold raw10736step4 raw10736step3; decide +kernel
      have hl : raw10736step3Labels = labelEmbedding1 ∘ raw10736step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10736step3 raw10736step3Labels raw10736step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw10737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10737step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw10737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10737step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10737step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10737step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10737step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10737 raw10737Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw10737 raw10737Labels = mixedMoment B raw10737step0 raw10737step0Labels := by
      have hz : ∀ j, raw10737 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10737step0 = (fun i j => raw10737 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10737step0 raw10737; decide +kernel
      have hl : raw10737step0Labels = raw10737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10737 raw10737Labels permutation434 hz
    mixedMoment B raw10737step0 raw10737step0Labels = mixedMoment B raw10737step1 raw10737step1Labels := by
      have hz : ∀ j, raw10737step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10737step1 = (fun i j => raw10737step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10737step1 raw10737step0; decide +kernel
      have hl : raw10737step1Labels = raw10737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10737step0 raw10737step0Labels permutation80 hz
    mixedMoment B raw10737step1 raw10737step1Labels = mixedMoment B raw10737step2 raw10737step2Labels := by
      have ha : raw10737step2 = (fun i j => raw10737step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10737step2 raw10737step1; decide +kernel
      have hl : raw10737step2Labels = raw10737step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10737step1 raw10737step1Labels permutation13 permutation7
    mixedMoment B raw10737step2 raw10737step2Labels = mixedMoment B raw10737step3 raw10737step3Labels := by
      have ha : raw10737step3 = -raw10737step2 := by apply Matrix.ext; change ∀ i j, raw10737step3 i j = -(raw10737step2 i j); unfold raw10737step3 raw10737step2; decide +kernel
      have hl : raw10737step3Labels = raw10737step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10737step3 raw10737step3Labels = mixedMoment B raw10737step4 raw10737step4Labels := by
      have ha : raw10737step4 = raw10737step3 := by apply Matrix.ext; unfold raw10737step4 raw10737step3; decide +kernel
      have hl : raw10737step3Labels = labelEmbedding1 ∘ raw10737step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10737step3 raw10737step3Labels raw10737step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw10738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw10738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10738 raw10738Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw10738 raw10738Labels = mixedMoment B raw10738step0 raw10738step0Labels := by
      have hz : ∀ j, raw10738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10738step0 = (fun i j => raw10738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10738step0 raw10738; decide +kernel
      have hl : raw10738step0Labels = raw10738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10738 raw10738Labels permutation434 hz
    mixedMoment B raw10738step0 raw10738step0Labels = mixedMoment B raw10738step1 raw10738step1Labels := by
      have ha : raw10738step1 = (fun i j => raw10738step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10738step1 raw10738step0; decide +kernel
      have hl : raw10738step1Labels = raw10738step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10738step0 raw10738step0Labels permutation43 permutation7
    mixedMoment B raw10738step1 raw10738step1Labels = mixedMoment B raw10738step2 raw10738step2Labels := by
      have ha : raw10738step2 = -raw10738step1 := by apply Matrix.ext; change ∀ i j, raw10738step2 i j = -(raw10738step1 i j); unfold raw10738step2 raw10738step1; decide +kernel
      have hl : raw10738step2Labels = raw10738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10738step2 raw10738step2Labels = mixedMoment B raw10738step3 raw10738step3Labels := by
      have ha : raw10738step3 = raw10738step2 := by apply Matrix.ext; unfold raw10738step3 raw10738step2; decide +kernel
      have hl : raw10738step2Labels = labelEmbedding1 ∘ raw10738step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10738step2 raw10738step2Labels raw10738step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw10739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw10739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10739 raw10739Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw10739 raw10739Labels = mixedMoment B raw10739step0 raw10739step0Labels := by
      have hz : ∀ j, raw10739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10739step0 = (fun i j => raw10739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10739step0 raw10739; decide +kernel
      have hl : raw10739step0Labels = raw10739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10739 raw10739Labels permutation346 hz
    mixedMoment B raw10739step0 raw10739step0Labels = mixedMoment B raw10739step1 raw10739step1Labels := by
      have ha : raw10739step1 = (fun i j => raw10739step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10739step1 raw10739step0; decide +kernel
      have hl : raw10739step1Labels = raw10739step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10739step0 raw10739step0Labels permutation43 permutation7
    mixedMoment B raw10739step1 raw10739step1Labels = mixedMoment B raw10739step2 raw10739step2Labels := by
      have ha : raw10739step2 = -raw10739step1 := by apply Matrix.ext; change ∀ i j, raw10739step2 i j = -(raw10739step1 i j); unfold raw10739step2 raw10739step1; decide +kernel
      have hl : raw10739step2Labels = raw10739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10739step2 raw10739step2Labels = mixedMoment B raw10739step3 raw10739step3Labels := by
      have ha : raw10739step3 = raw10739step2 := by apply Matrix.ext; unfold raw10739step3 raw10739step2; decide +kernel
      have hl : raw10739step2Labels = labelEmbedding1 ∘ raw10739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10739step2 raw10739step2Labels raw10739step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw10740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw10740step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10740step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw10740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10740step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10740step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10740step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10740step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10740 raw10740Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw10740 raw10740Labels = mixedMoment B raw10740step0 raw10740step0Labels := by
      have hz : ∀ j, raw10740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10740step0 = (fun i j => raw10740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10740step0 raw10740; decide +kernel
      have hl : raw10740step0Labels = raw10740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10740 raw10740Labels permutation434 hz
    mixedMoment B raw10740step0 raw10740step0Labels = mixedMoment B raw10740step1 raw10740step1Labels := by
      have hz : ∀ j, raw10740step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10740step1 = (fun i j => raw10740step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10740step1 raw10740step0; decide +kernel
      have hl : raw10740step1Labels = raw10740step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10740step0 raw10740step0Labels permutation80 hz
    mixedMoment B raw10740step1 raw10740step1Labels = mixedMoment B raw10740step2 raw10740step2Labels := by
      have ha : raw10740step2 = (fun i j => raw10740step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10740step2 raw10740step1; decide +kernel
      have hl : raw10740step2Labels = raw10740step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10740step1 raw10740step1Labels permutation13 permutation7
    mixedMoment B raw10740step2 raw10740step2Labels = mixedMoment B raw10740step3 raw10740step3Labels := by
      have ha : raw10740step3 = -raw10740step2 := by apply Matrix.ext; change ∀ i j, raw10740step3 i j = -(raw10740step2 i j); unfold raw10740step3 raw10740step2; decide +kernel
      have hl : raw10740step3Labels = raw10740step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10740step3 raw10740step3Labels = mixedMoment B raw10740step4 raw10740step4Labels := by
      have ha : raw10740step4 = raw10740step3 := by apply Matrix.ext; unfold raw10740step4 raw10740step3; decide +kernel
      have hl : raw10740step3Labels = labelEmbedding1 ∘ raw10740step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10740step3 raw10740step3Labels raw10740step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw10741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw10741step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10741step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10741step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10741step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10741step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10741 raw10741Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw10741 raw10741Labels = mixedMoment B raw10741step0 raw10741step0Labels := by
      have hz : ∀ j, raw10741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10741step0 = (fun i j => raw10741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10741step0 raw10741; decide +kernel
      have hl : raw10741step0Labels = raw10741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10741 raw10741Labels permutation434 hz
    mixedMoment B raw10741step0 raw10741step0Labels = mixedMoment B raw10741step1 raw10741step1Labels := by
      have hz : ∀ j, raw10741step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10741step1 = (fun i j => raw10741step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10741step1 raw10741step0; decide +kernel
      have hl : raw10741step1Labels = raw10741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10741step0 raw10741step0Labels permutation80 hz
    mixedMoment B raw10741step1 raw10741step1Labels = mixedMoment B raw10741step2 raw10741step2Labels := by
      have ha : raw10741step2 = (fun i j => raw10741step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10741step2 raw10741step1; decide +kernel
      have hl : raw10741step2Labels = raw10741step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10741step1 raw10741step1Labels permutation13 permutation7
    mixedMoment B raw10741step2 raw10741step2Labels = mixedMoment B raw10741step3 raw10741step3Labels := by
      have ha : raw10741step3 = -raw10741step2 := by apply Matrix.ext; change ∀ i j, raw10741step3 i j = -(raw10741step2 i j); unfold raw10741step3 raw10741step2; decide +kernel
      have hl : raw10741step3Labels = raw10741step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10741step3 raw10741step3Labels = mixedMoment B raw10741step4 raw10741step4Labels := by
      have ha : raw10741step4 = raw10741step3 := by apply Matrix.ext; unfold raw10741step4 raw10741step3; decide +kernel
      have hl : raw10741step3Labels = labelEmbedding1 ∘ raw10741step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10741step3 raw10741step3Labels raw10741step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw10742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10742 raw10742Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw10742 raw10742Labels = mixedMoment B raw10742step0 raw10742step0Labels := by
      have hz : ∀ j, raw10742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10742step0 = (fun i j => raw10742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10742step0 raw10742; decide +kernel
      have hl : raw10742step0Labels = raw10742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10742 raw10742Labels permutation434 hz
    mixedMoment B raw10742step0 raw10742step0Labels = mixedMoment B raw10742step1 raw10742step1Labels := by
      have ha : raw10742step1 = (fun i j => raw10742step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10742step1 raw10742step0; decide +kernel
      have hl : raw10742step1Labels = raw10742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10742step0 raw10742step0Labels permutation43 permutation7
    mixedMoment B raw10742step1 raw10742step1Labels = mixedMoment B raw10742step2 raw10742step2Labels := by
      have ha : raw10742step2 = -raw10742step1 := by apply Matrix.ext; change ∀ i j, raw10742step2 i j = -(raw10742step1 i j); unfold raw10742step2 raw10742step1; decide +kernel
      have hl : raw10742step2Labels = raw10742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10742step2 raw10742step2Labels = mixedMoment B raw10742step3 raw10742step3Labels := by
      have ha : raw10742step3 = raw10742step2 := by apply Matrix.ext; unfold raw10742step3 raw10742step2; decide +kernel
      have hl : raw10742step2Labels = labelEmbedding1 ∘ raw10742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10742step2 raw10742step2Labels raw10742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw10743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw10743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10743 raw10743Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw10743 raw10743Labels = mixedMoment B raw10743step0 raw10743step0Labels := by
      have hz : ∀ j, raw10743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10743step0 = (fun i j => raw10743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10743step0 raw10743; decide +kernel
      have hl : raw10743step0Labels = raw10743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10743 raw10743Labels permutation434 hz
    mixedMoment B raw10743step0 raw10743step0Labels = mixedMoment B raw10743step1 raw10743step1Labels := by
      have ha : raw10743step1 = (fun i j => raw10743step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10743step1 raw10743step0; decide +kernel
      have hl : raw10743step1Labels = raw10743step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10743step0 raw10743step0Labels permutation43 permutation7
    mixedMoment B raw10743step1 raw10743step1Labels = mixedMoment B raw10743step2 raw10743step2Labels := by
      have ha : raw10743step2 = -raw10743step1 := by apply Matrix.ext; change ∀ i j, raw10743step2 i j = -(raw10743step1 i j); unfold raw10743step2 raw10743step1; decide +kernel
      have hl : raw10743step2Labels = raw10743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10743step2 raw10743step2Labels = mixedMoment B raw10743step3 raw10743step3Labels := by
      have ha : raw10743step3 = raw10743step2 := by apply Matrix.ext; unfold raw10743step3 raw10743step2; decide +kernel
      have hl : raw10743step2Labels = labelEmbedding1 ∘ raw10743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10743step2 raw10743step2Labels raw10743step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw10744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10744step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10744 raw10744Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw10744 raw10744Labels = mixedMoment B raw10744step0 raw10744step0Labels := by
      have ha : raw10744step0 = (fun i j => raw10744 (permutation211 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10744step0 raw10744; decide +kernel
      have hl : raw10744step0Labels = raw10744Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10744 raw10744Labels permutation211 permutation7
    mixedMoment B raw10744step0 raw10744step0Labels = mixedMoment B raw10744step1 raw10744step1Labels := by
      have ha : raw10744step1 = -raw10744step0 := by apply Matrix.ext; change ∀ i j, raw10744step1 i j = -(raw10744step0 i j); unfold raw10744step1 raw10744step0; decide +kernel
      have hl : raw10744step1Labels = raw10744step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10744step1 raw10744step1Labels = mixedMoment B raw10744step2 raw10744step2Labels := by
      have ha : raw10744step2 = raw10744step1 := by apply Matrix.ext; unfold raw10744step2 raw10744step1; decide +kernel
      have hl : raw10744step1Labels = labelEmbedding1 ∘ raw10744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10744step1 raw10744step1Labels raw10744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw10745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw10745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10745 raw10745Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw10745 raw10745Labels = mixedMoment B raw10745step0 raw10745step0Labels := by
      have hz : ∀ j, raw10745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10745step0 = (fun i j => raw10745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10745step0 raw10745; decide +kernel
      have hl : raw10745step0Labels = raw10745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10745 raw10745Labels permutation434 hz
    mixedMoment B raw10745step0 raw10745step0Labels = mixedMoment B raw10745step1 raw10745step1Labels := by
      have ha : raw10745step1 = (fun i j => raw10745step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10745step1 raw10745step0; decide +kernel
      have hl : raw10745step1Labels = raw10745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10745step0 raw10745step0Labels permutation43 permutation7
    mixedMoment B raw10745step1 raw10745step1Labels = mixedMoment B raw10745step2 raw10745step2Labels := by
      have ha : raw10745step2 = -raw10745step1 := by apply Matrix.ext; change ∀ i j, raw10745step2 i j = -(raw10745step1 i j); unfold raw10745step2 raw10745step1; decide +kernel
      have hl : raw10745step2Labels = raw10745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10745step2 raw10745step2Labels = mixedMoment B raw10745step3 raw10745step3Labels := by
      have ha : raw10745step3 = raw10745step2 := by apply Matrix.ext; unfold raw10745step3 raw10745step2; decide +kernel
      have hl : raw10745step2Labels = labelEmbedding1 ∘ raw10745step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10745step2 raw10745step2Labels raw10745step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw10746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10746step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10746step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10746 raw10746Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw10746 raw10746Labels = mixedMoment B raw10746step0 raw10746step0Labels := by
      have hz : ∀ j, raw10746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10746step0 = (fun i j => raw10746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10746step0 raw10746; decide +kernel
      have hl : raw10746step0Labels = raw10746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10746 raw10746Labels permutation434 hz
    mixedMoment B raw10746step0 raw10746step0Labels = mixedMoment B raw10746step1 raw10746step1Labels := by
      have ha : raw10746step1 = (fun i j => raw10746step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10746step1 raw10746step0; decide +kernel
      have hl : raw10746step1Labels = raw10746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10746step0 raw10746step0Labels permutation43 permutation7
    mixedMoment B raw10746step1 raw10746step1Labels = mixedMoment B raw10746step2 raw10746step2Labels := by
      have ha : raw10746step2 = -raw10746step1 := by apply Matrix.ext; change ∀ i j, raw10746step2 i j = -(raw10746step1 i j); unfold raw10746step2 raw10746step1; decide +kernel
      have hl : raw10746step2Labels = raw10746step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10746step2 raw10746step2Labels = mixedMoment B raw10746step3 raw10746step3Labels := by
      have ha : raw10746step3 = raw10746step2 := by apply Matrix.ext; unfold raw10746step3 raw10746step2; decide +kernel
      have hl : raw10746step2Labels = labelEmbedding1 ∘ raw10746step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10746step2 raw10746step2Labels raw10746step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw10747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10747 raw10747Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw10747 raw10747Labels = mixedMoment B raw10747step0 raw10747step0Labels := by
      have hz : ∀ j, raw10747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10747step0 = (fun i j => raw10747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10747step0 raw10747; decide +kernel
      have hl : raw10747step0Labels = raw10747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10747 raw10747Labels permutation346 hz
    mixedMoment B raw10747step0 raw10747step0Labels = mixedMoment B raw10747step1 raw10747step1Labels := by
      have ha : raw10747step1 = (fun i j => raw10747step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10747step1 raw10747step0; decide +kernel
      have hl : raw10747step1Labels = raw10747step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10747step0 raw10747step0Labels permutation43 permutation7
    mixedMoment B raw10747step1 raw10747step1Labels = mixedMoment B raw10747step2 raw10747step2Labels := by
      have ha : raw10747step2 = -raw10747step1 := by apply Matrix.ext; change ∀ i j, raw10747step2 i j = -(raw10747step1 i j); unfold raw10747step2 raw10747step1; decide +kernel
      have hl : raw10747step2Labels = raw10747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10747step2 raw10747step2Labels = mixedMoment B raw10747step3 raw10747step3Labels := by
      have ha : raw10747step3 = raw10747step2 := by apply Matrix.ext; unfold raw10747step3 raw10747step2; decide +kernel
      have hl : raw10747step2Labels = labelEmbedding1 ∘ raw10747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10747step2 raw10747step2Labels raw10747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw10748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw10748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw10748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10748 raw10748Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw10748 raw10748Labels = mixedMoment B raw10748step0 raw10748step0Labels := by
      have hz : ∀ j, raw10748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10748step0 = (fun i j => raw10748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10748step0 raw10748; decide +kernel
      have hl : raw10748step0Labels = raw10748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10748 raw10748Labels permutation346 hz
    mixedMoment B raw10748step0 raw10748step0Labels = mixedMoment B raw10748step1 raw10748step1Labels := by
      have ha : raw10748step1 = (fun i j => raw10748step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10748step1 raw10748step0; decide +kernel
      have hl : raw10748step1Labels = raw10748step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10748step0 raw10748step0Labels permutation43 permutation7
    mixedMoment B raw10748step1 raw10748step1Labels = mixedMoment B raw10748step2 raw10748step2Labels := by
      have ha : raw10748step2 = -raw10748step1 := by apply Matrix.ext; change ∀ i j, raw10748step2 i j = -(raw10748step1 i j); unfold raw10748step2 raw10748step1; decide +kernel
      have hl : raw10748step2Labels = raw10748step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10748step2 raw10748step2Labels = mixedMoment B raw10748step3 raw10748step3Labels := by
      have ha : raw10748step3 = raw10748step2 := by apply Matrix.ext; unfold raw10748step3 raw10748step2; decide +kernel
      have hl : raw10748step2Labels = labelEmbedding1 ∘ raw10748step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10748step2 raw10748step2Labels raw10748step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw10749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10749step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10749 raw10749Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw10749 raw10749Labels = mixedMoment B raw10749step0 raw10749step0Labels := by
      have ha : raw10749step0 = (fun i j => raw10749 (permutation187 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10749step0 raw10749; decide +kernel
      have hl : raw10749step0Labels = raw10749Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10749 raw10749Labels permutation187 permutation7
    mixedMoment B raw10749step0 raw10749step0Labels = mixedMoment B raw10749step1 raw10749step1Labels := by
      have ha : raw10749step1 = -raw10749step0 := by apply Matrix.ext; change ∀ i j, raw10749step1 i j = -(raw10749step0 i j); unfold raw10749step1 raw10749step0; decide +kernel
      have hl : raw10749step1Labels = raw10749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10749step1 raw10749step1Labels = mixedMoment B raw10749step2 raw10749step2Labels := by
      have ha : raw10749step2 = raw10749step1 := by apply Matrix.ext; unfold raw10749step2 raw10749step1; decide +kernel
      have hl : raw10749step1Labels = labelEmbedding1 ∘ raw10749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10749step1 raw10749step1Labels raw10749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw10750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw10750step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10750step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10750 raw10750Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw10750 raw10750Labels = mixedMoment B raw10750step0 raw10750step0Labels := by
      have hz : ∀ j, raw10750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10750step0 = (fun i j => raw10750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10750step0 raw10750; decide +kernel
      have hl : raw10750step0Labels = raw10750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10750 raw10750Labels permutation346 hz
    mixedMoment B raw10750step0 raw10750step0Labels = mixedMoment B raw10750step1 raw10750step1Labels := by
      have ha : raw10750step1 = (fun i j => raw10750step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10750step1 raw10750step0; decide +kernel
      have hl : raw10750step1Labels = raw10750step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10750step0 raw10750step0Labels permutation43 permutation7
    mixedMoment B raw10750step1 raw10750step1Labels = mixedMoment B raw10750step2 raw10750step2Labels := by
      have ha : raw10750step2 = -raw10750step1 := by apply Matrix.ext; change ∀ i j, raw10750step2 i j = -(raw10750step1 i j); unfold raw10750step2 raw10750step1; decide +kernel
      have hl : raw10750step2Labels = raw10750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10750step2 raw10750step2Labels = mixedMoment B raw10750step3 raw10750step3Labels := by
      have ha : raw10750step3 = raw10750step2 := by apply Matrix.ext; unfold raw10750step3 raw10750step2; decide +kernel
      have hl : raw10750step2Labels = labelEmbedding1 ∘ raw10750step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10750step2 raw10750step2Labels raw10750step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw10751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10751step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10751step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10751step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10751 raw10751Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw10751 raw10751Labels = mixedMoment B raw10751step0 raw10751step0Labels := by
      have hz : ∀ j, raw10751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10751step0 = (fun i j => raw10751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10751step0 raw10751; decide +kernel
      have hl : raw10751step0Labels = raw10751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10751 raw10751Labels permutation346 hz
    mixedMoment B raw10751step0 raw10751step0Labels = mixedMoment B raw10751step1 raw10751step1Labels := by
      have ha : raw10751step1 = (fun i j => raw10751step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10751step1 raw10751step0; decide +kernel
      have hl : raw10751step1Labels = raw10751step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10751step0 raw10751step0Labels permutation43 permutation7
    mixedMoment B raw10751step1 raw10751step1Labels = mixedMoment B raw10751step2 raw10751step2Labels := by
      have ha : raw10751step2 = -raw10751step1 := by apply Matrix.ext; change ∀ i j, raw10751step2 i j = -(raw10751step1 i j); unfold raw10751step2 raw10751step1; decide +kernel
      have hl : raw10751step2Labels = raw10751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10751step2 raw10751step2Labels = mixedMoment B raw10751step3 raw10751step3Labels := by
      have ha : raw10751step3 = raw10751step2 := by apply Matrix.ext; unfold raw10751step3 raw10751step2; decide +kernel
      have hl : raw10751step2Labels = labelEmbedding1 ∘ raw10751step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10751step2 raw10751step2Labels raw10751step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2245 node2245Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
