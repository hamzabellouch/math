import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26624 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26624step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26624 raw26624Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26624 raw26624Labels = mixedMoment B raw26624step0 raw26624step0Labels := by
      have hz : ∀ j, raw26624 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26624step0 = (fun i j => raw26624 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26624step0 raw26624; decide +kernel
      have hl : raw26624step0Labels = raw26624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26624 raw26624Labels permutation265 hz
    mixedMoment B raw26624step0 raw26624step0Labels = mixedMoment B raw26624step1 raw26624step1Labels := by
      have ha : raw26624step1 = (fun i j => raw26624step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26624step1 raw26624step0; decide +kernel
      have hl : raw26624step1Labels = raw26624step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26624step0 raw26624step0Labels permutation53 permutation7
    mixedMoment B raw26624step1 raw26624step1Labels = mixedMoment B raw26624step2 raw26624step2Labels := by
      have ha : raw26624step2 = raw26624step1 := by apply Matrix.ext; unfold raw26624step2 raw26624step1; decide +kernel
      have hl : raw26624step1Labels = labelEmbedding1 ∘ raw26624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26624step1 raw26624step1Labels raw26624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw26625 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26625 raw26625Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26625 raw26625Labels = mixedMoment B raw26625step0 raw26625step0Labels := by
      have hz : ∀ j, raw26625 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26625step0 = (fun i j => raw26625 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26625step0 raw26625; decide +kernel
      have hl : raw26625step0Labels = raw26625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26625 raw26625Labels permutation265 hz
    mixedMoment B raw26625step0 raw26625step0Labels = mixedMoment B raw26625step1 raw26625step1Labels := by
      have ha : raw26625step1 = (fun i j => raw26625step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26625step1 raw26625step0; decide +kernel
      have hl : raw26625step1Labels = raw26625step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26625step0 raw26625step0Labels permutation52 permutation7
    mixedMoment B raw26625step1 raw26625step1Labels = mixedMoment B raw26625step2 raw26625step2Labels := by
      have ha : raw26625step2 = raw26625step1 := by apply Matrix.ext; unfold raw26625step2 raw26625step1; decide +kernel
      have hl : raw26625step1Labels = labelEmbedding1 ∘ raw26625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26625step1 raw26625step1Labels raw26625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw26626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26626 raw26626Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26626 raw26626Labels = mixedMoment B raw26626step0 raw26626step0Labels := by
      have hz : ∀ j, raw26626 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26626step0 = (fun i j => raw26626 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26626step0 raw26626; decide +kernel
      have hl : raw26626step0Labels = raw26626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26626 raw26626Labels permutation265 hz
    mixedMoment B raw26626step0 raw26626step0Labels = mixedMoment B raw26626step1 raw26626step1Labels := by
      have ha : raw26626step1 = (fun i j => raw26626step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26626step1 raw26626step0; decide +kernel
      have hl : raw26626step1Labels = raw26626step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26626step0 raw26626step0Labels permutation42 permutation7
    mixedMoment B raw26626step1 raw26626step1Labels = mixedMoment B raw26626step2 raw26626step2Labels := by
      have ha : raw26626step2 = raw26626step1 := by apply Matrix.ext; unfold raw26626step2 raw26626step1; decide +kernel
      have hl : raw26626step1Labels = labelEmbedding1 ∘ raw26626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26626step1 raw26626step1Labels raw26626step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw26627 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26627 raw26627Labels = mixedMoment B node1441 node1441Labels := by
  calc
    mixedMoment B raw26627 raw26627Labels = mixedMoment B raw26627step0 raw26627step0Labels := by
      have hz : ∀ j, raw26627 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26627step0 = (fun i j => raw26627 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26627step0 raw26627; decide +kernel
      have hl : raw26627step0Labels = raw26627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26627 raw26627Labels permutation265 hz
    mixedMoment B raw26627step0 raw26627step0Labels = mixedMoment B raw26627step1 raw26627step1Labels := by
      have ha : raw26627step1 = (fun i j => raw26627step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26627step1 raw26627step0; decide +kernel
      have hl : raw26627step1Labels = raw26627step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26627step0 raw26627step0Labels permutation54 permutation7
    mixedMoment B raw26627step1 raw26627step1Labels = mixedMoment B raw26627step2 raw26627step2Labels := by
      have ha : raw26627step2 = raw26627step1 := by apply Matrix.ext; unfold raw26627step2 raw26627step1; decide +kernel
      have hl : raw26627step1Labels = labelEmbedding1 ∘ raw26627step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26627step1 raw26627step1Labels raw26627step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1441 node1441Labels := by rfl

def raw26628 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26628 raw26628Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26628 raw26628Labels = mixedMoment B raw26628step0 raw26628step0Labels := by
      have ha : raw26628step0 = (fun i j => raw26628 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26628step0 raw26628; decide +kernel
      have hl : raw26628step0Labels = raw26628Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26628 raw26628Labels permutation174 permutation7
    mixedMoment B raw26628step0 raw26628step0Labels = mixedMoment B raw26628step1 raw26628step1Labels := by
      have ha : raw26628step1 = raw26628step0 := by apply Matrix.ext; unfold raw26628step1 raw26628step0; decide +kernel
      have hl : raw26628step0Labels = labelEmbedding1 ∘ raw26628step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26628step0 raw26628step0Labels raw26628step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw26629 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26629 raw26629Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26629 raw26629Labels = mixedMoment B raw26629step0 raw26629step0Labels := by
      have hz : ∀ j, raw26629 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26629step0 = (fun i j => raw26629 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26629step0 raw26629; decide +kernel
      have hl : raw26629step0Labels = raw26629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26629 raw26629Labels permutation265 hz
    mixedMoment B raw26629step0 raw26629step0Labels = mixedMoment B raw26629step1 raw26629step1Labels := by
      have ha : raw26629step1 = (fun i j => raw26629step0 (permutation55 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26629step1 raw26629step0; decide +kernel
      have hl : raw26629step1Labels = raw26629step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26629step0 raw26629step0Labels permutation55 permutation7
    mixedMoment B raw26629step1 raw26629step1Labels = mixedMoment B raw26629step2 raw26629step2Labels := by
      have ha : raw26629step2 = raw26629step1 := by apply Matrix.ext; unfold raw26629step2 raw26629step1; decide +kernel
      have hl : raw26629step1Labels = labelEmbedding1 ∘ raw26629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26629step1 raw26629step1Labels raw26629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw26630 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26630step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26630 raw26630Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26630 raw26630Labels = mixedMoment B raw26630step0 raw26630step0Labels := by
      have hz : ∀ j, raw26630 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26630step0 = (fun i j => raw26630 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26630step0 raw26630; decide +kernel
      have hl : raw26630step0Labels = raw26630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26630 raw26630Labels permutation265 hz
    mixedMoment B raw26630step0 raw26630step0Labels = mixedMoment B raw26630step1 raw26630step1Labels := by
      have ha : raw26630step1 = (fun i j => raw26630step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26630step1 raw26630step0; decide +kernel
      have hl : raw26630step1Labels = raw26630step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26630step0 raw26630step0Labels permutation54 permutation7
    mixedMoment B raw26630step1 raw26630step1Labels = mixedMoment B raw26630step2 raw26630step2Labels := by
      have ha : raw26630step2 = raw26630step1 := by apply Matrix.ext; unfold raw26630step2 raw26630step1; decide +kernel
      have hl : raw26630step1Labels = labelEmbedding1 ∘ raw26630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26630step1 raw26630step1Labels raw26630step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw26631 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26631step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26631 raw26631Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26631 raw26631Labels = mixedMoment B raw26631step0 raw26631step0Labels := by
      have hz : ∀ j, raw26631 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26631step0 = (fun i j => raw26631 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26631step0 raw26631; decide +kernel
      have hl : raw26631step0Labels = raw26631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26631 raw26631Labels permutation265 hz
    mixedMoment B raw26631step0 raw26631step0Labels = mixedMoment B raw26631step1 raw26631step1Labels := by
      have ha : raw26631step1 = (fun i j => raw26631step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26631step1 raw26631step0; decide +kernel
      have hl : raw26631step1Labels = raw26631step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26631step0 raw26631step0Labels permutation48 permutation7
    mixedMoment B raw26631step1 raw26631step1Labels = mixedMoment B raw26631step2 raw26631step2Labels := by
      have ha : raw26631step2 = raw26631step1 := by apply Matrix.ext; unfold raw26631step2 raw26631step1; decide +kernel
      have hl : raw26631step1Labels = labelEmbedding1 ∘ raw26631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26631step1 raw26631step1Labels raw26631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw26632 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26632 raw26632Labels = mixedMoment B node1435 node1435Labels := by
  calc
    mixedMoment B raw26632 raw26632Labels = mixedMoment B raw26632step0 raw26632step0Labels := by
      have hz : ∀ j, raw26632 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26632step0 = (fun i j => raw26632 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26632step0 raw26632; decide +kernel
      have hl : raw26632step0Labels = raw26632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26632 raw26632Labels permutation265 hz
    mixedMoment B raw26632step0 raw26632step0Labels = mixedMoment B raw26632step1 raw26632step1Labels := by
      have ha : raw26632step1 = (fun i j => raw26632step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26632step1 raw26632step0; decide +kernel
      have hl : raw26632step1Labels = raw26632step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26632step0 raw26632step0Labels permutation50 permutation7
    mixedMoment B raw26632step1 raw26632step1Labels = mixedMoment B raw26632step2 raw26632step2Labels := by
      have ha : raw26632step2 = raw26632step1 := by apply Matrix.ext; unfold raw26632step2 raw26632step1; decide +kernel
      have hl : raw26632step1Labels = labelEmbedding1 ∘ raw26632step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26632step1 raw26632step1Labels raw26632step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1435 node1435Labels := by rfl

def raw26633 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26633step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26633 raw26633Labels = mixedMoment B node1256 node1256Labels := by
  calc
    mixedMoment B raw26633 raw26633Labels = mixedMoment B raw26633step0 raw26633step0Labels := by
      have ha : raw26633step0 = (fun i j => raw26633 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26633step0 raw26633; decide +kernel
      have hl : raw26633step0Labels = raw26633Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26633 raw26633Labels permutation170 permutation7
    mixedMoment B raw26633step0 raw26633step0Labels = mixedMoment B raw26633step1 raw26633step1Labels := by
      have ha : raw26633step1 = raw26633step0 := by apply Matrix.ext; unfold raw26633step1 raw26633step0; decide +kernel
      have hl : raw26633step0Labels = labelEmbedding1 ∘ raw26633step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26633step0 raw26633step0Labels raw26633step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1256 node1256Labels := by rfl

def raw26634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26634step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26634 raw26634Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw26634 raw26634Labels = mixedMoment B raw26634step0 raw26634step0Labels := by
      have hz : ∀ j, raw26634 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26634step0 = (fun i j => raw26634 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26634step0 raw26634; decide +kernel
      have hl : raw26634step0Labels = raw26634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26634 raw26634Labels permutation265 hz
    mixedMoment B raw26634step0 raw26634step0Labels = mixedMoment B raw26634step1 raw26634step1Labels := by
      have ha : raw26634step1 = (fun i j => raw26634step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26634step1 raw26634step0; decide +kernel
      have hl : raw26634step1Labels = raw26634step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26634step0 raw26634step0Labels permutation53 permutation7
    mixedMoment B raw26634step1 raw26634step1Labels = mixedMoment B raw26634step2 raw26634step2Labels := by
      have ha : raw26634step2 = raw26634step1 := by apply Matrix.ext; unfold raw26634step2 raw26634step1; decide +kernel
      have hl : raw26634step1Labels = labelEmbedding1 ∘ raw26634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26634step1 raw26634step1Labels raw26634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1286 node1286Labels := by rfl

def raw26635 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26635 raw26635Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw26635 raw26635Labels = mixedMoment B raw26635step0 raw26635step0Labels := by
      have hz : ∀ j, raw26635 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26635step0 = (fun i j => raw26635 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26635step0 raw26635; decide +kernel
      have hl : raw26635step0Labels = raw26635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26635 raw26635Labels permutation265 hz
    mixedMoment B raw26635step0 raw26635step0Labels = mixedMoment B raw26635step1 raw26635step1Labels := by
      have ha : raw26635step1 = (fun i j => raw26635step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26635step1 raw26635step0; decide +kernel
      have hl : raw26635step1Labels = raw26635step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26635step0 raw26635step0Labels permutation51 permutation7
    mixedMoment B raw26635step1 raw26635step1Labels = mixedMoment B raw26635step2 raw26635step2Labels := by
      have ha : raw26635step2 = raw26635step1 := by apply Matrix.ext; unfold raw26635step2 raw26635step1; decide +kernel
      have hl : raw26635step1Labels = labelEmbedding1 ∘ raw26635step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26635step1 raw26635step1Labels raw26635step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1286 node1286Labels := by rfl

def raw26636 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw26636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw26636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26636step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26636 raw26636Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw26636 raw26636Labels = mixedMoment B raw26636step0 raw26636step0Labels := by
      have hz : ∀ j, raw26636 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26636step0 = (fun i j => raw26636 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26636step0 raw26636; decide +kernel
      have hl : raw26636step0Labels = raw26636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26636 raw26636Labels permutation265 hz
    mixedMoment B raw26636step0 raw26636step0Labels = mixedMoment B raw26636step1 raw26636step1Labels := by
      have ha : raw26636step1 = (fun i j => raw26636step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26636step1 raw26636step0; decide +kernel
      have hl : raw26636step1Labels = raw26636step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26636step0 raw26636step0Labels permutation50 permutation7
    mixedMoment B raw26636step1 raw26636step1Labels = mixedMoment B raw26636step2 raw26636step2Labels := by
      have ha : raw26636step2 = raw26636step1 := by apply Matrix.ext; unfold raw26636step2 raw26636step1; decide +kernel
      have hl : raw26636step1Labels = labelEmbedding1 ∘ raw26636step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26636step1 raw26636step1Labels raw26636step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1286 node1286Labels := by rfl

def raw26637 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26637 raw26637Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw26637 raw26637Labels = mixedMoment B raw26637step0 raw26637step0Labels := by
      have hz : ∀ j, raw26637 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26637step0 = (fun i j => raw26637 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26637step0 raw26637; decide +kernel
      have hl : raw26637step0Labels = raw26637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26637 raw26637Labels permutation265 hz
    mixedMoment B raw26637step0 raw26637step0Labels = mixedMoment B raw26637step1 raw26637step1Labels := by
      have ha : raw26637step1 = (fun i j => raw26637step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26637step1 raw26637step0; decide +kernel
      have hl : raw26637step1Labels = raw26637step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26637step0 raw26637step0Labels permutation51 permutation2
    mixedMoment B raw26637step1 raw26637step1Labels = mixedMoment B raw26637step2 raw26637step2Labels := by
      have ha : raw26637step2 = -raw26637step1 := by apply Matrix.ext; change ∀ i j, raw26637step2 i j = -(raw26637step1 i j); unfold raw26637step2 raw26637step1; decide +kernel
      have hl : raw26637step2Labels = raw26637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1648 node1648Labels := by rfl

def raw26638 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26638 raw26638Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw26638 raw26638Labels = mixedMoment B raw26638step0 raw26638step0Labels := by
      have hz : ∀ j, raw26638 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26638step0 = (fun i j => raw26638 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26638step0 raw26638; decide +kernel
      have hl : raw26638step0Labels = raw26638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26638 raw26638Labels permutation265 hz
    mixedMoment B raw26638step0 raw26638step0Labels = mixedMoment B raw26638step1 raw26638step1Labels := by
      have ha : raw26638step1 = (fun i j => raw26638step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26638step1 raw26638step0; decide +kernel
      have hl : raw26638step1Labels = raw26638step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26638step0 raw26638step0Labels permutation50 permutation2
    mixedMoment B raw26638step1 raw26638step1Labels = mixedMoment B raw26638step2 raw26638step2Labels := by
      have ha : raw26638step2 = -raw26638step1 := by apply Matrix.ext; change ∀ i j, raw26638step2 i j = -(raw26638step1 i j); unfold raw26638step2 raw26638step1; decide +kernel
      have hl : raw26638step2Labels = raw26638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1648 node1648Labels := by rfl

def raw26639 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26639 raw26639Labels = mixedMoment B node1726 node1726Labels := by
  calc
    mixedMoment B raw26639 raw26639Labels = mixedMoment B raw26639step0 raw26639step0Labels := by
      have hz : ∀ j, raw26639 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26639step0 = (fun i j => raw26639 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26639step0 raw26639; decide +kernel
      have hl : raw26639step0Labels = raw26639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26639 raw26639Labels permutation265 hz
    mixedMoment B raw26639step0 raw26639step0Labels = mixedMoment B raw26639step1 raw26639step1Labels := by
      have ha : raw26639step1 = (fun i j => raw26639step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26639step1 raw26639step0; decide +kernel
      have hl : raw26639step1Labels = raw26639step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26639step0 raw26639step0Labels permutation50 permutation2
    mixedMoment B raw26639step1 raw26639step1Labels = mixedMoment B raw26639step2 raw26639step2Labels := by
      have ha : raw26639step2 = -raw26639step1 := by apply Matrix.ext; change ∀ i j, raw26639step2 i j = -(raw26639step1 i j); unfold raw26639step2 raw26639step1; decide +kernel
      have hl : raw26639step2Labels = raw26639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1726 node1726Labels := by rfl

def raw26640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26640 raw26640Labels = mixedMoment B node5167 node5167Labels := by
  calc
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw26641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26641 raw26641Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw26641 raw26641Labels = mixedMoment B raw26641step0 raw26641step0Labels := by
      have hz : ∀ j, raw26641 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26641step0 = (fun i j => raw26641 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26641step0 raw26641; decide +kernel
      have hl : raw26641step0Labels = raw26641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26641 raw26641Labels permutation265 hz
    mixedMoment B raw26641step0 raw26641step0Labels = mixedMoment B raw26641step1 raw26641step1Labels := by
      have ha : raw26641step1 = (fun i j => raw26641step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26641step1 raw26641step0; decide +kernel
      have hl : raw26641step1Labels = raw26641step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26641step0 raw26641step0Labels permutation44 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw26642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26642 raw26642Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw26642 raw26642Labels = mixedMoment B raw26642step0 raw26642step0Labels := by
      have hz : ∀ j, raw26642 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26642step0 = (fun i j => raw26642 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26642step0 raw26642; decide +kernel
      have hl : raw26642step0Labels = raw26642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26642 raw26642Labels permutation265 hz
    mixedMoment B raw26642step0 raw26642step0Labels = mixedMoment B raw26642step1 raw26642step1Labels := by
      have ha : raw26642step1 = (fun i j => raw26642step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26642step1 raw26642step0; decide +kernel
      have hl : raw26642step1Labels = raw26642step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26642step0 raw26642step0Labels permutation50 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw26643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26643step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26643 raw26643Labels = mixedMoment B node4171 node4171Labels := by
  calc
    mixedMoment B raw26643 raw26643Labels = mixedMoment B raw26643step0 raw26643step0Labels := by
      have ha : raw26643step0 = (fun i j => raw26643 (permutation240 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26643step0 raw26643; decide +kernel
      have hl : raw26643step0Labels = raw26643Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26643 raw26643Labels permutation240 permutation3
    mixedMoment B raw26643step0 raw26643step0Labels = mixedMoment B raw26643step1 raw26643step1Labels := by
      have ha : raw26643step1 = raw26643step0 := by apply Matrix.ext; unfold raw26643step1 raw26643step0; decide +kernel
      have hl : raw26643step0Labels = labelEmbedding6 ∘ raw26643step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26643step0 raw26643step0Labels raw26643step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4171 node4171Labels := by rfl

def raw26644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26644 raw26644Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26644 raw26644Labels = mixedMoment B raw26644step0 raw26644step0Labels := by
      have hz : ∀ j, raw26644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26644step0 = (fun i j => raw26644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26644step0 raw26644; decide +kernel
      have hl : raw26644step0Labels = raw26644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26644 raw26644Labels permutation434 hz
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw26645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26645step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26645 raw26645Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26645 raw26645Labels = mixedMoment B raw26645step0 raw26645step0Labels := by
      have ha : raw26645step0 = (fun i j => raw26645 (permutation240 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26645step0 raw26645; decide +kernel
      have hl : raw26645step0Labels = raw26645Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26645 raw26645Labels permutation240 permutation3
    mixedMoment B raw26645step0 raw26645step0Labels = mixedMoment B raw26645step1 raw26645step1Labels := by
      have ha : raw26645step1 = raw26645step0 := by apply Matrix.ext; unfold raw26645step1 raw26645step0; decide +kernel
      have hl : raw26645step0Labels = labelEmbedding6 ∘ raw26645step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26645step0 raw26645step0Labels raw26645step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw26646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26646step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26646 raw26646Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26646 raw26646Labels = mixedMoment B raw26646step0 raw26646step0Labels := by
      have ha : raw26646step0 = (fun i j => raw26646 (permutation260 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26646step0 raw26646; decide +kernel
      have hl : raw26646step0Labels = raw26646Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26646 raw26646Labels permutation260 permutation3
    mixedMoment B raw26646step0 raw26646step0Labels = mixedMoment B raw26646step1 raw26646step1Labels := by
      have ha : raw26646step1 = raw26646step0 := by apply Matrix.ext; unfold raw26646step1 raw26646step0; decide +kernel
      have hl : raw26646step0Labels = labelEmbedding6 ∘ raw26646step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26646step0 raw26646step0Labels raw26646step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw26647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26647step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26647step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26647 raw26647Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw26647 raw26647Labels = mixedMoment B raw26647step0 raw26647step0Labels := by
      have hz : ∀ j, raw26647 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26647step0 = (fun i j => raw26647 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26647step0 raw26647; decide +kernel
      have hl : raw26647step0Labels = raw26647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26647 raw26647Labels permutation265 hz
    mixedMoment B raw26647step0 raw26647step0Labels = mixedMoment B raw26647step1 raw26647step1Labels := by
      have ha : raw26647step1 = (fun i j => raw26647step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26647step1 raw26647step0; decide +kernel
      have hl : raw26647step1Labels = raw26647step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26647step0 raw26647step0Labels permutation49 permutation3
    mixedMoment B raw26647step1 raw26647step1Labels = mixedMoment B raw26647step2 raw26647step2Labels := by
      have ha : raw26647step2 = raw26647step1 := by apply Matrix.ext; unfold raw26647step2 raw26647step1; decide +kernel
      have hl : raw26647step1Labels = labelEmbedding6 ∘ raw26647step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26647step1 raw26647step1Labels raw26647step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4172 node4172Labels := by rfl

def raw26648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26648step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26648 raw26648Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw26648 raw26648Labels = mixedMoment B raw26648step0 raw26648step0Labels := by
      have ha : raw26648step0 = (fun i j => raw26648 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26648step0 raw26648; decide +kernel
      have hl : raw26648step0Labels = raw26648Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26648 raw26648Labels permutation169 permutation3
    mixedMoment B raw26648step0 raw26648step0Labels = mixedMoment B raw26648step1 raw26648step1Labels := by
      have ha : raw26648step1 = raw26648step0 := by apply Matrix.ext; unfold raw26648step1 raw26648step0; decide +kernel
      have hl : raw26648step0Labels = labelEmbedding6 ∘ raw26648step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26648step0 raw26648step0Labels raw26648step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4541 node4541Labels := by rfl

def raw26649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26649step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26649step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26649 raw26649Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw26649 raw26649Labels = mixedMoment B raw26649step0 raw26649step0Labels := by
      have hz : ∀ j, raw26649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26649step0 = (fun i j => raw26649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26649step0 raw26649; decide +kernel
      have hl : raw26649step0Labels = raw26649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26649 raw26649Labels permutation434 hz
    mixedMoment B raw26649step0 raw26649step0Labels = mixedMoment B raw26649step1 raw26649step1Labels := by
      have hz : ∀ j, raw26649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26649step1 = (fun i j => raw26649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26649step1 raw26649step0; decide +kernel
      have hl : raw26649step1Labels = raw26649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26649step0 raw26649step0Labels permutation56 hz
    mixedMoment B raw26649step1 raw26649step1Labels = mixedMoment B raw26649step2 raw26649step2Labels := by
      have ha : raw26649step2 = (fun i j => raw26649step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26649step2 raw26649step1; decide +kernel
      have hl : raw26649step2Labels = raw26649step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26649step1 raw26649step1Labels permutation11 permutation3
    mixedMoment B raw26649step2 raw26649step2Labels = mixedMoment B raw26649step3 raw26649step3Labels := by
      have ha : raw26649step3 = raw26649step2 := by apply Matrix.ext; unfold raw26649step3 raw26649step2; decide +kernel
      have hl : raw26649step2Labels = labelEmbedding6 ∘ raw26649step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26649step2 raw26649step2Labels raw26649step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw26650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26650step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26650 raw26650Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26650 raw26650Labels = mixedMoment B raw26650step0 raw26650step0Labels := by
      have hz : ∀ j, raw26650 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26650step0 = (fun i j => raw26650 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26650step0 raw26650; decide +kernel
      have hl : raw26650step0Labels = raw26650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26650 raw26650Labels permutation265 hz
    mixedMoment B raw26650step0 raw26650step0Labels = mixedMoment B raw26650step1 raw26650step1Labels := by
      have ha : raw26650step1 = (fun i j => raw26650step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26650step1 raw26650step0; decide +kernel
      have hl : raw26650step1Labels = raw26650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26650step0 raw26650step0Labels permutation49 permutation3
    mixedMoment B raw26650step1 raw26650step1Labels = mixedMoment B raw26650step2 raw26650step2Labels := by
      have ha : raw26650step2 = raw26650step1 := by apply Matrix.ext; unfold raw26650step2 raw26650step1; decide +kernel
      have hl : raw26650step1Labels = labelEmbedding6 ∘ raw26650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26650step1 raw26650step1Labels raw26650step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw26651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26651step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26651 raw26651Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26651 raw26651Labels = mixedMoment B raw26651step0 raw26651step0Labels := by
      have hz : ∀ j, raw26651 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26651step0 = (fun i j => raw26651 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26651step0 raw26651; decide +kernel
      have hl : raw26651step0Labels = raw26651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26651 raw26651Labels permutation265 hz
    mixedMoment B raw26651step0 raw26651step0Labels = mixedMoment B raw26651step1 raw26651step1Labels := by
      have ha : raw26651step1 = (fun i j => raw26651step0 (permutation55 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26651step1 raw26651step0; decide +kernel
      have hl : raw26651step1Labels = raw26651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26651step0 raw26651step0Labels permutation55 permutation3
    mixedMoment B raw26651step1 raw26651step1Labels = mixedMoment B raw26651step2 raw26651step2Labels := by
      have ha : raw26651step2 = raw26651step1 := by apply Matrix.ext; unfold raw26651step2 raw26651step1; decide +kernel
      have hl : raw26651step1Labels = labelEmbedding6 ∘ raw26651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26651step1 raw26651step1Labels raw26651step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw26652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26652step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26652 raw26652Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw26652 raw26652Labels = mixedMoment B raw26652step0 raw26652step0Labels := by
      have hz : ∀ j, raw26652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26652step0 = (fun i j => raw26652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26652step0 raw26652; decide +kernel
      have hl : raw26652step0Labels = raw26652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26652 raw26652Labels permutation265 hz
    mixedMoment B raw26652step0 raw26652step0Labels = mixedMoment B raw26652step1 raw26652step1Labels := by
      have ha : raw26652step1 = (fun i j => raw26652step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26652step1 raw26652step0; decide +kernel
      have hl : raw26652step1Labels = raw26652step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26652step0 raw26652step0Labels permutation48 permutation3
    mixedMoment B raw26652step1 raw26652step1Labels = mixedMoment B raw26652step2 raw26652step2Labels := by
      have ha : raw26652step2 = raw26652step1 := by apply Matrix.ext; unfold raw26652step2 raw26652step1; decide +kernel
      have hl : raw26652step1Labels = labelEmbedding6 ∘ raw26652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26652step1 raw26652step1Labels raw26652step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4172 node4172Labels := by rfl

def raw26653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26653step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26653 raw26653Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw26653 raw26653Labels = mixedMoment B raw26653step0 raw26653step0Labels := by
      have ha : raw26653step0 = (fun i j => raw26653 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26653step0 raw26653; decide +kernel
      have hl : raw26653step0Labels = raw26653Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26653 raw26653Labels permutation168 permutation3
    mixedMoment B raw26653step0 raw26653step0Labels = mixedMoment B raw26653step1 raw26653step1Labels := by
      have ha : raw26653step1 = raw26653step0 := by apply Matrix.ext; unfold raw26653step1 raw26653step0; decide +kernel
      have hl : raw26653step0Labels = labelEmbedding6 ∘ raw26653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26653step0 raw26653step0Labels raw26653step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4541 node4541Labels := by rfl

def raw26654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26654step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26654step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26654 raw26654Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26654 raw26654Labels = mixedMoment B raw26654step0 raw26654step0Labels := by
      have hz : ∀ j, raw26654 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26654step0 = (fun i j => raw26654 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26654step0 raw26654; decide +kernel
      have hl : raw26654step0Labels = raw26654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26654 raw26654Labels permutation265 hz
    mixedMoment B raw26654step0 raw26654step0Labels = mixedMoment B raw26654step1 raw26654step1Labels := by
      have ha : raw26654step1 = (fun i j => raw26654step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26654step1 raw26654step0; decide +kernel
      have hl : raw26654step1Labels = raw26654step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26654step0 raw26654step0Labels permutation48 permutation3
    mixedMoment B raw26654step1 raw26654step1Labels = mixedMoment B raw26654step2 raw26654step2Labels := by
      have ha : raw26654step2 = raw26654step1 := by apply Matrix.ext; unfold raw26654step2 raw26654step1; decide +kernel
      have hl : raw26654step1Labels = labelEmbedding6 ∘ raw26654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26654step1 raw26654step1Labels raw26654step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw26655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26655step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26655 raw26655Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26655 raw26655Labels = mixedMoment B raw26655step0 raw26655step0Labels := by
      have hz : ∀ j, raw26655 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26655step0 = (fun i j => raw26655 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26655step0 raw26655; decide +kernel
      have hl : raw26655step0Labels = raw26655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26655 raw26655Labels permutation265 hz
    mixedMoment B raw26655step0 raw26655step0Labels = mixedMoment B raw26655step1 raw26655step1Labels := by
      have ha : raw26655step1 = (fun i j => raw26655step0 (permutation54 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26655step1 raw26655step0; decide +kernel
      have hl : raw26655step1Labels = raw26655step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26655step0 raw26655step0Labels permutation54 permutation3
    mixedMoment B raw26655step1 raw26655step1Labels = mixedMoment B raw26655step2 raw26655step2Labels := by
      have ha : raw26655step2 = raw26655step1 := by apply Matrix.ext; unfold raw26655step2 raw26655step1; decide +kernel
      have hl : raw26655step1Labels = labelEmbedding6 ∘ raw26655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26655step1 raw26655step1Labels raw26655step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw26656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26656step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26656 raw26656Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw26656 raw26656Labels = mixedMoment B raw26656step0 raw26656step0Labels := by
      have hz : ∀ j, raw26656 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26656step0 = (fun i j => raw26656 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26656step0 raw26656; decide +kernel
      have hl : raw26656step0Labels = raw26656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26656 raw26656Labels permutation265 hz
    mixedMoment B raw26656step0 raw26656step0Labels = mixedMoment B raw26656step1 raw26656step1Labels := by
      have ha : raw26656step1 = (fun i j => raw26656step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26656step1 raw26656step0; decide +kernel
      have hl : raw26656step1Labels = raw26656step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26656step0 raw26656step0Labels permutation50 permutation3
    mixedMoment B raw26656step1 raw26656step1Labels = mixedMoment B raw26656step2 raw26656step2Labels := by
      have ha : raw26656step2 = raw26656step1 := by apply Matrix.ext; unfold raw26656step2 raw26656step1; decide +kernel
      have hl : raw26656step1Labels = labelEmbedding6 ∘ raw26656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26656step1 raw26656step1Labels raw26656step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw26657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26657step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26657 raw26657Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw26657 raw26657Labels = mixedMoment B raw26657step0 raw26657step0Labels := by
      have ha : raw26657step0 = (fun i j => raw26657 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26657step0 raw26657; decide +kernel
      have hl : raw26657step0Labels = raw26657Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26657 raw26657Labels permutation170 permutation3
    mixedMoment B raw26657step0 raw26657step0Labels = mixedMoment B raw26657step1 raw26657step1Labels := by
      have ha : raw26657step1 = raw26657step0 := by apply Matrix.ext; unfold raw26657step1 raw26657step0; decide +kernel
      have hl : raw26657step0Labels = labelEmbedding6 ∘ raw26657step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26657step0 raw26657step0Labels raw26657step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4544 node4544Labels := by rfl

def raw26658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw26658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw26658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26658 raw26658Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26658 raw26658Labels = mixedMoment B raw26658step0 raw26658step0Labels := by
      have hz : ∀ j, raw26658 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26658step0 = (fun i j => raw26658 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26658step0 raw26658; decide +kernel
      have hl : raw26658step0Labels = raw26658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26658 raw26658Labels permutation265 hz
    mixedMoment B raw26658step0 raw26658step0Labels = mixedMoment B raw26658step1 raw26658step1Labels := by
      have ha : raw26658step1 = (fun i j => raw26658step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26658step1 raw26658step0; decide +kernel
      have hl : raw26658step1Labels = raw26658step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26658step0 raw26658step0Labels permutation50 permutation3
    mixedMoment B raw26658step1 raw26658step1Labels = mixedMoment B raw26658step2 raw26658step2Labels := by
      have ha : raw26658step2 = raw26658step1 := by apply Matrix.ext; unfold raw26658step2 raw26658step1; decide +kernel
      have hl : raw26658step1Labels = labelEmbedding6 ∘ raw26658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26658step1 raw26658step1Labels raw26658step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw26659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26659 raw26659Labels = mixedMoment B node2958 node2958Labels := by
  calc
    mixedMoment B raw26659 raw26659Labels = mixedMoment B raw26659step0 raw26659step0Labels := by
      have ha : raw26659step0 = (fun i j => raw26659 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26659step0 raw26659; decide +kernel
      have hl : raw26659step0Labels = raw26659Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26659 raw26659Labels permutation168 permutation3
    _ = mixedMoment B node2958 node2958Labels := by rfl

def raw26660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26660 raw26660Labels = mixedMoment B node3122 node3122Labels := by
  calc
    mixedMoment B raw26660 raw26660Labels = mixedMoment B raw26660step0 raw26660step0Labels := by
      have hz : ∀ j, raw26660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26660step0 = (fun i j => raw26660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26660step0 raw26660; decide +kernel
      have hl : raw26660step0Labels = raw26660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26660 raw26660Labels permutation434 hz
    mixedMoment B raw26660step0 raw26660step0Labels = mixedMoment B raw26660step1 raw26660step1Labels := by
      have hz : ∀ j, raw26660step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26660step1 = (fun i j => raw26660step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26660step1 raw26660step0; decide +kernel
      have hl : raw26660step1Labels = raw26660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26660step0 raw26660step0Labels permutation56 hz
    mixedMoment B raw26660step1 raw26660step1Labels = mixedMoment B raw26660step2 raw26660step2Labels := by
      have ha : raw26660step2 = (fun i j => raw26660step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26660step2 raw26660step1; decide +kernel
      have hl : raw26660step2Labels = raw26660step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26660step1 raw26660step1Labels permutation11 permutation3
    _ = mixedMoment B node3122 node3122Labels := by rfl

def raw26661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26661 raw26661Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw26661 raw26661Labels = mixedMoment B raw26661step0 raw26661step0Labels := by
      have hz : ∀ j, raw26661 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26661step0 = (fun i j => raw26661 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26661step0 raw26661; decide +kernel
      have hl : raw26661step0Labels = raw26661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26661 raw26661Labels permutation265 hz
    mixedMoment B raw26661step0 raw26661step0Labels = mixedMoment B raw26661step1 raw26661step1Labels := by
      have ha : raw26661step1 = (fun i j => raw26661step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26661step1 raw26661step0; decide +kernel
      have hl : raw26661step1Labels = raw26661step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26661step0 raw26661step0Labels permutation48 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw26662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26662 raw26662Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw26662 raw26662Labels = mixedMoment B raw26662step0 raw26662step0Labels := by
      have hz : ∀ j, raw26662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26662step0 = (fun i j => raw26662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26662step0 raw26662; decide +kernel
      have hl : raw26662step0Labels = raw26662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26662 raw26662Labels permutation265 hz
    mixedMoment B raw26662step0 raw26662step0Labels = mixedMoment B raw26662step1 raw26662step1Labels := by
      have ha : raw26662step1 = (fun i j => raw26662step0 (permutation54 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26662step1 raw26662step0; decide +kernel
      have hl : raw26662step1Labels = raw26662step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26662step0 raw26662step0Labels permutation54 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw26663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26663 raw26663Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw26663 raw26663Labels = mixedMoment B raw26663step0 raw26663step0Labels := by
      have ha : raw26663step0 = (fun i j => raw26663 (permutation240 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26663step0 raw26663; decide +kernel
      have hl : raw26663step0Labels = raw26663Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26663 raw26663Labels permutation240 permutation3
    _ = mixedMoment B node599 node599Labels := by rfl

def raw26664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26664 raw26664Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26664 raw26664Labels = mixedMoment B raw26664step0 raw26664step0Labels := by
      have hz : ∀ j, raw26664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26664step0 = (fun i j => raw26664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26664step0 raw26664; decide +kernel
      have hl : raw26664step0Labels = raw26664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26664 raw26664Labels permutation434 hz
    mixedMoment B raw26664step0 raw26664step0Labels = mixedMoment B raw26664step1 raw26664step1Labels := by
      have ha : raw26664step1 = (fun i j => raw26664step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26664step1 raw26664step0; decide +kernel
      have hl : raw26664step1Labels = raw26664step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26664step0 raw26664step0Labels permutation48 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw26665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26665 raw26665Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw26665 raw26665Labels = mixedMoment B raw26665step0 raw26665step0Labels := by
      have ha : raw26665step0 = (fun i j => raw26665 (permutation240 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26665step0 raw26665; decide +kernel
      have hl : raw26665step0Labels = raw26665Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26665 raw26665Labels permutation240 permutation3
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw26666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26666 raw26666Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw26666 raw26666Labels = mixedMoment B raw26666step0 raw26666step0Labels := by
      have ha : raw26666step0 = (fun i j => raw26666 (permutation260 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26666step0 raw26666; decide +kernel
      have hl : raw26666step0Labels = raw26666Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26666 raw26666Labels permutation260 permutation3
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw26667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26667 raw26667Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw26667 raw26667Labels = mixedMoment B raw26667step0 raw26667step0Labels := by
      have hz : ∀ j, raw26667 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26667step0 = (fun i j => raw26667 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26667step0 raw26667; decide +kernel
      have hl : raw26667step0Labels = raw26667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26667 raw26667Labels permutation265 hz
    mixedMoment B raw26667step0 raw26667step0Labels = mixedMoment B raw26667step1 raw26667step1Labels := by
      have ha : raw26667step1 = (fun i j => raw26667step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26667step1 raw26667step0; decide +kernel
      have hl : raw26667step1Labels = raw26667step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26667step0 raw26667step0Labels permutation49 permutation3
    _ = mixedMoment B node600 node600Labels := by rfl

def raw26668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26668 raw26668Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw26668 raw26668Labels = mixedMoment B raw26668step0 raw26668step0Labels := by
      have ha : raw26668step0 = (fun i j => raw26668 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26668step0 raw26668; decide +kernel
      have hl : raw26668step0Labels = raw26668Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26668 raw26668Labels permutation169 permutation3
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw26669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26669step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26669 raw26669Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw26669 raw26669Labels = mixedMoment B raw26669step0 raw26669step0Labels := by
      have hz : ∀ j, raw26669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26669step0 = (fun i j => raw26669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26669step0 raw26669; decide +kernel
      have hl : raw26669step0Labels = raw26669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26669 raw26669Labels permutation434 hz
    mixedMoment B raw26669step0 raw26669step0Labels = mixedMoment B raw26669step1 raw26669step1Labels := by
      have hz : ∀ j, raw26669step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26669step1 = (fun i j => raw26669step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26669step1 raw26669step0; decide +kernel
      have hl : raw26669step1Labels = raw26669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26669step0 raw26669step0Labels permutation56 hz
    mixedMoment B raw26669step1 raw26669step1Labels = mixedMoment B raw26669step2 raw26669step2Labels := by
      have ha : raw26669step2 = (fun i j => raw26669step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26669step2 raw26669step1; decide +kernel
      have hl : raw26669step2Labels = raw26669step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26669step1 raw26669step1Labels permutation11 permutation3
    _ = mixedMoment B node1300 node1300Labels := by rfl

def raw26670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26670 raw26670Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26670 raw26670Labels = mixedMoment B raw26670step0 raw26670step0Labels := by
      have hz : ∀ j, raw26670 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26670step0 = (fun i j => raw26670 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26670step0 raw26670; decide +kernel
      have hl : raw26670step0Labels = raw26670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26670 raw26670Labels permutation265 hz
    mixedMoment B raw26670step0 raw26670step0Labels = mixedMoment B raw26670step1 raw26670step1Labels := by
      have ha : raw26670step1 = (fun i j => raw26670step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26670step1 raw26670step0; decide +kernel
      have hl : raw26670step1Labels = raw26670step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26670step0 raw26670step0Labels permutation49 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw26671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26671 raw26671Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26671 raw26671Labels = mixedMoment B raw26671step0 raw26671step0Labels := by
      have hz : ∀ j, raw26671 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26671step0 = (fun i j => raw26671 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26671step0 raw26671; decide +kernel
      have hl : raw26671step0Labels = raw26671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26671 raw26671Labels permutation265 hz
    mixedMoment B raw26671step0 raw26671step0Labels = mixedMoment B raw26671step1 raw26671step1Labels := by
      have ha : raw26671step1 = (fun i j => raw26671step0 (permutation55 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26671step1 raw26671step0; decide +kernel
      have hl : raw26671step1Labels = raw26671step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26671step0 raw26671step0Labels permutation55 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw26672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26672 raw26672Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw26672 raw26672Labels = mixedMoment B raw26672step0 raw26672step0Labels := by
      have hz : ∀ j, raw26672 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26672step0 = (fun i j => raw26672 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26672step0 raw26672; decide +kernel
      have hl : raw26672step0Labels = raw26672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26672 raw26672Labels permutation265 hz
    mixedMoment B raw26672step0 raw26672step0Labels = mixedMoment B raw26672step1 raw26672step1Labels := by
      have ha : raw26672step1 = (fun i j => raw26672step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26672step1 raw26672step0; decide +kernel
      have hl : raw26672step1Labels = raw26672step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26672step0 raw26672step0Labels permutation48 permutation3
    _ = mixedMoment B node600 node600Labels := by rfl

def raw26673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26673 raw26673Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw26673 raw26673Labels = mixedMoment B raw26673step0 raw26673step0Labels := by
      have ha : raw26673step0 = (fun i j => raw26673 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26673step0 raw26673; decide +kernel
      have hl : raw26673step0Labels = raw26673Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26673 raw26673Labels permutation168 permutation3
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw26674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26674step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26674step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26674 raw26674Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26674 raw26674Labels = mixedMoment B raw26674step0 raw26674step0Labels := by
      have hz : ∀ j, raw26674 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26674step0 = (fun i j => raw26674 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26674step0 raw26674; decide +kernel
      have hl : raw26674step0Labels = raw26674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26674 raw26674Labels permutation265 hz
    mixedMoment B raw26674step0 raw26674step0Labels = mixedMoment B raw26674step1 raw26674step1Labels := by
      have ha : raw26674step1 = (fun i j => raw26674step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26674step1 raw26674step0; decide +kernel
      have hl : raw26674step1Labels = raw26674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26674step0 raw26674step0Labels permutation48 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw26675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26675 raw26675Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26675 raw26675Labels = mixedMoment B raw26675step0 raw26675step0Labels := by
      have hz : ∀ j, raw26675 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26675step0 = (fun i j => raw26675 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26675step0 raw26675; decide +kernel
      have hl : raw26675step0Labels = raw26675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26675 raw26675Labels permutation265 hz
    mixedMoment B raw26675step0 raw26675step0Labels = mixedMoment B raw26675step1 raw26675step1Labels := by
      have ha : raw26675step1 = (fun i j => raw26675step0 (permutation54 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26675step1 raw26675step0; decide +kernel
      have hl : raw26675step1Labels = raw26675step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26675step0 raw26675step0Labels permutation54 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw26676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26676step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26676step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26676 raw26676Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw26676 raw26676Labels = mixedMoment B raw26676step0 raw26676step0Labels := by
      have hz : ∀ j, raw26676 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26676step0 = (fun i j => raw26676 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26676step0 raw26676; decide +kernel
      have hl : raw26676step0Labels = raw26676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26676 raw26676Labels permutation265 hz
    mixedMoment B raw26676step0 raw26676step0Labels = mixedMoment B raw26676step1 raw26676step1Labels := by
      have ha : raw26676step1 = (fun i j => raw26676step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26676step1 raw26676step0; decide +kernel
      have hl : raw26676step1Labels = raw26676step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26676step0 raw26676step0Labels permutation50 permutation3
    _ = mixedMoment B node603 node603Labels := by rfl

def raw26677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26677 raw26677Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw26677 raw26677Labels = mixedMoment B raw26677step0 raw26677step0Labels := by
      have ha : raw26677step0 = (fun i j => raw26677 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26677step0 raw26677; decide +kernel
      have hl : raw26677step0Labels = raw26677Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26677 raw26677Labels permutation170 permutation3
    _ = mixedMoment B node1129 node1129Labels := by rfl

def raw26678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw26678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw26678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26678 raw26678Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw26678 raw26678Labels = mixedMoment B raw26678step0 raw26678step0Labels := by
      have hz : ∀ j, raw26678 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26678step0 = (fun i j => raw26678 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26678step0 raw26678; decide +kernel
      have hl : raw26678step0Labels = raw26678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26678 raw26678Labels permutation265 hz
    mixedMoment B raw26678step0 raw26678step0Labels = mixedMoment B raw26678step1 raw26678step1Labels := by
      have ha : raw26678step1 = (fun i j => raw26678step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26678step1 raw26678step0; decide +kernel
      have hl : raw26678step1Labels = raw26678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26678step0 raw26678step0Labels permutation50 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw26679 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26679step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26679 raw26679Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw26679 raw26679Labels = mixedMoment B raw26679step0 raw26679step0Labels := by
      have ha : raw26679step0 = (fun i j => raw26679 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26679step0 raw26679; decide +kernel
      have hl : raw26679step0Labels = raw26679Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26679 raw26679Labels permutation168 permutation7
    mixedMoment B raw26679step0 raw26679step0Labels = mixedMoment B raw26679step1 raw26679step1Labels := by
      have ha : raw26679step1 = raw26679step0 := by apply Matrix.ext; unfold raw26679step1 raw26679step0; decide +kernel
      have hl : raw26679step0Labels = labelEmbedding10 ∘ raw26679step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26679step0 raw26679step0Labels raw26679step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw26680 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26680step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26680 raw26680Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26680 raw26680Labels = mixedMoment B raw26680step0 raw26680step0Labels := by
      have hz : ∀ j, raw26680 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26680step0 = (fun i j => raw26680 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26680step0 raw26680; decide +kernel
      have hl : raw26680step0Labels = raw26680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26680 raw26680Labels permutation265 hz
    mixedMoment B raw26680step0 raw26680step0Labels = mixedMoment B raw26680step1 raw26680step1Labels := by
      have ha : raw26680step1 = (fun i j => raw26680step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26680step1 raw26680step0; decide +kernel
      have hl : raw26680step1Labels = raw26680step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26680step0 raw26680step0Labels permutation49 permutation7
    mixedMoment B raw26680step1 raw26680step1Labels = mixedMoment B raw26680step2 raw26680step2Labels := by
      have ha : raw26680step2 = raw26680step1 := by apply Matrix.ext; unfold raw26680step2 raw26680step1; decide +kernel
      have hl : raw26680step1Labels = labelEmbedding10 ∘ raw26680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26680step1 raw26680step1Labels raw26680step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw26681 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26681step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26681 raw26681Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26681 raw26681Labels = mixedMoment B raw26681step0 raw26681step0Labels := by
      have hz : ∀ j, raw26681 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26681step0 = (fun i j => raw26681 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26681step0 raw26681; decide +kernel
      have hl : raw26681step0Labels = raw26681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26681 raw26681Labels permutation265 hz
    mixedMoment B raw26681step0 raw26681step0Labels = mixedMoment B raw26681step1 raw26681step1Labels := by
      have ha : raw26681step1 = (fun i j => raw26681step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26681step1 raw26681step0; decide +kernel
      have hl : raw26681step1Labels = raw26681step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26681step0 raw26681step0Labels permutation48 permutation7
    mixedMoment B raw26681step1 raw26681step1Labels = mixedMoment B raw26681step2 raw26681step2Labels := by
      have ha : raw26681step2 = raw26681step1 := by apply Matrix.ext; unfold raw26681step2 raw26681step1; decide +kernel
      have hl : raw26681step1Labels = labelEmbedding10 ∘ raw26681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26681step1 raw26681step1Labels raw26681step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw26682 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26682step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26682 raw26682Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26682 raw26682Labels = mixedMoment B raw26682step0 raw26682step0Labels := by
      have hz : ∀ j, raw26682 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26682step0 = (fun i j => raw26682 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26682step0 raw26682; decide +kernel
      have hl : raw26682step0Labels = raw26682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26682 raw26682Labels permutation265 hz
    mixedMoment B raw26682step0 raw26682step0Labels = mixedMoment B raw26682step1 raw26682step1Labels := by
      have ha : raw26682step1 = (fun i j => raw26682step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26682step1 raw26682step0; decide +kernel
      have hl : raw26682step1Labels = raw26682step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26682step0 raw26682step0Labels permutation44 permutation7
    mixedMoment B raw26682step1 raw26682step1Labels = mixedMoment B raw26682step2 raw26682step2Labels := by
      have ha : raw26682step2 = raw26682step1 := by apply Matrix.ext; unfold raw26682step2 raw26682step1; decide +kernel
      have hl : raw26682step1Labels = labelEmbedding10 ∘ raw26682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26682step1 raw26682step1Labels raw26682step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw26683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26683step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26683 raw26683Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw26683 raw26683Labels = mixedMoment B raw26683step0 raw26683step0Labels := by
      have ha : raw26683step0 = (fun i j => raw26683 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26683step0 raw26683; decide +kernel
      have hl : raw26683step0Labels = raw26683Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26683 raw26683Labels permutation152 permutation6
    mixedMoment B raw26683step0 raw26683step0Labels = mixedMoment B raw26683step1 raw26683step1Labels := by
      have ha : raw26683step1 = raw26683step0 := by apply Matrix.ext; unfold raw26683step1 raw26683step0; decide +kernel
      have hl : raw26683step0Labels = labelEmbedding9 ∘ raw26683step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26683step0 raw26683step0Labels raw26683step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw26684 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26684step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26684 raw26684Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26684 raw26684Labels = mixedMoment B raw26684step0 raw26684step0Labels := by
      have ha : raw26684step0 = (fun i j => raw26684 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26684step0 raw26684; decide +kernel
      have hl : raw26684step0Labels = raw26684Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26684 raw26684Labels permutation169 permutation7
    mixedMoment B raw26684step0 raw26684step0Labels = mixedMoment B raw26684step1 raw26684step1Labels := by
      have ha : raw26684step1 = raw26684step0 := by apply Matrix.ext; unfold raw26684step1 raw26684step0; decide +kernel
      have hl : raw26684step0Labels = labelEmbedding10 ∘ raw26684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26684step0 raw26684step0Labels raw26684step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26685 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26685step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26685step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26685 raw26685Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26685 raw26685Labels = mixedMoment B raw26685step0 raw26685step0Labels := by
      have ha : raw26685step0 = (fun i j => raw26685 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26685step0 raw26685; decide +kernel
      have hl : raw26685step0Labels = raw26685Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26685 raw26685Labels permutation168 permutation7
    mixedMoment B raw26685step0 raw26685step0Labels = mixedMoment B raw26685step1 raw26685step1Labels := by
      have ha : raw26685step1 = raw26685step0 := by apply Matrix.ext; unfold raw26685step1 raw26685step0; decide +kernel
      have hl : raw26685step0Labels = labelEmbedding10 ∘ raw26685step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26685step0 raw26685step0Labels raw26685step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26686 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26686step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26686 raw26686Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26686 raw26686Labels = mixedMoment B raw26686step0 raw26686step0Labels := by
      have ha : raw26686step0 = (fun i j => raw26686 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26686step0 raw26686; decide +kernel
      have hl : raw26686step0Labels = raw26686Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26686 raw26686Labels permutation164 permutation7
    mixedMoment B raw26686step0 raw26686step0Labels = mixedMoment B raw26686step1 raw26686step1Labels := by
      have ha : raw26686step1 = raw26686step0 := by apply Matrix.ext; unfold raw26686step1 raw26686step0; decide +kernel
      have hl : raw26686step0Labels = labelEmbedding10 ∘ raw26686step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26686step0 raw26686step0Labels raw26686step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw26687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26687step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26687 raw26687Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26687 raw26687Labels = mixedMoment B raw26687step0 raw26687step0Labels := by
      have hz : ∀ j, raw26687 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26687step0 = (fun i j => raw26687 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26687step0 raw26687; decide +kernel
      have hl : raw26687step0Labels = raw26687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26687 raw26687Labels permutation265 hz
    mixedMoment B raw26687step0 raw26687step0Labels = mixedMoment B raw26687step1 raw26687step1Labels := by
      have ha : raw26687step1 = (fun i j => raw26687step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26687step1 raw26687step0; decide +kernel
      have hl : raw26687step1Labels = raw26687step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26687step0 raw26687step0Labels permutation38 permutation6
    mixedMoment B raw26687step1 raw26687step1Labels = mixedMoment B raw26687step2 raw26687step2Labels := by
      have ha : raw26687step2 = raw26687step1 := by apply Matrix.ext; unfold raw26687step2 raw26687step1; decide +kernel
      have hl : raw26687step1Labels = labelEmbedding9 ∘ raw26687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26687step1 raw26687step1Labels raw26687step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw26688 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26688step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26688 raw26688Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26688 raw26688Labels = mixedMoment B raw26688step0 raw26688step0Labels := by
      have ha : raw26688step0 = (fun i j => raw26688 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26688step0 raw26688; decide +kernel
      have hl : raw26688step0Labels = raw26688Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26688 raw26688Labels permutation158 permutation6
    mixedMoment B raw26688step0 raw26688step0Labels = mixedMoment B raw26688step1 raw26688step1Labels := by
      have ha : raw26688step1 = raw26688step0 := by apply Matrix.ext; unfold raw26688step1 raw26688step0; decide +kernel
      have hl : raw26688step0Labels = labelEmbedding9 ∘ raw26688step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26688step0 raw26688step0Labels raw26688step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw26689 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26689step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26689 raw26689Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26689 raw26689Labels = mixedMoment B raw26689step0 raw26689step0Labels := by
      have hz : ∀ j, raw26689 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26689step0 = (fun i j => raw26689 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26689step0 raw26689; decide +kernel
      have hl : raw26689step0Labels = raw26689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26689 raw26689Labels permutation265 hz
    mixedMoment B raw26689step0 raw26689step0Labels = mixedMoment B raw26689step1 raw26689step1Labels := by
      have ha : raw26689step1 = (fun i j => raw26689step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26689step1 raw26689step0; decide +kernel
      have hl : raw26689step1Labels = raw26689step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26689step0 raw26689step0Labels permutation38 permutation6
    mixedMoment B raw26689step1 raw26689step1Labels = mixedMoment B raw26689step2 raw26689step2Labels := by
      have ha : raw26689step2 = raw26689step1 := by apply Matrix.ext; unfold raw26689step2 raw26689step1; decide +kernel
      have hl : raw26689step1Labels = labelEmbedding9 ∘ raw26689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26689step1 raw26689step1Labels raw26689step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw26690 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26690step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26690 raw26690Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26690 raw26690Labels = mixedMoment B raw26690step0 raw26690step0Labels := by
      have hz : ∀ j, raw26690 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26690step0 = (fun i j => raw26690 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26690step0 raw26690; decide +kernel
      have hl : raw26690step0Labels = raw26690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26690 raw26690Labels permutation265 hz
    mixedMoment B raw26690step0 raw26690step0Labels = mixedMoment B raw26690step1 raw26690step1Labels := by
      have ha : raw26690step1 = (fun i j => raw26690step0 (permutation42 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26690step1 raw26690step0; decide +kernel
      have hl : raw26690step1Labels = raw26690step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26690step0 raw26690step0Labels permutation42 permutation6
    mixedMoment B raw26690step1 raw26690step1Labels = mixedMoment B raw26690step2 raw26690step2Labels := by
      have ha : raw26690step2 = raw26690step1 := by apply Matrix.ext; unfold raw26690step2 raw26690step1; decide +kernel
      have hl : raw26690step1Labels = labelEmbedding9 ∘ raw26690step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26690step1 raw26690step1Labels raw26690step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw26691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26691step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26691 raw26691Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26691 raw26691Labels = mixedMoment B raw26691step0 raw26691step0Labels := by
      have hz : ∀ j, raw26691 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26691step0 = (fun i j => raw26691 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26691step0 raw26691; decide +kernel
      have hl : raw26691step0Labels = raw26691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26691 raw26691Labels permutation265 hz
    mixedMoment B raw26691step0 raw26691step0Labels = mixedMoment B raw26691step1 raw26691step1Labels := by
      have ha : raw26691step1 = (fun i j => raw26691step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26691step1 raw26691step0; decide +kernel
      have hl : raw26691step1Labels = raw26691step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26691step0 raw26691step0Labels permutation32 permutation6
    mixedMoment B raw26691step1 raw26691step1Labels = mixedMoment B raw26691step2 raw26691step2Labels := by
      have ha : raw26691step2 = raw26691step1 := by apply Matrix.ext; unfold raw26691step2 raw26691step1; decide +kernel
      have hl : raw26691step1Labels = labelEmbedding9 ∘ raw26691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26691step1 raw26691step1Labels raw26691step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw26692 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26692step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26692 raw26692Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26692 raw26692Labels = mixedMoment B raw26692step0 raw26692step0Labels := by
      have ha : raw26692step0 = (fun i j => raw26692 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26692step0 raw26692; decide +kernel
      have hl : raw26692step0Labels = raw26692Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26692 raw26692Labels permutation152 permutation6
    mixedMoment B raw26692step0 raw26692step0Labels = mixedMoment B raw26692step1 raw26692step1Labels := by
      have ha : raw26692step1 = raw26692step0 := by apply Matrix.ext; unfold raw26692step1 raw26692step0; decide +kernel
      have hl : raw26692step0Labels = labelEmbedding9 ∘ raw26692step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26692step0 raw26692step0Labels raw26692step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw26693 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26693step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26693 raw26693Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26693 raw26693Labels = mixedMoment B raw26693step0 raw26693step0Labels := by
      have hz : ∀ j, raw26693 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26693step0 = (fun i j => raw26693 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26693step0 raw26693; decide +kernel
      have hl : raw26693step0Labels = raw26693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26693 raw26693Labels permutation265 hz
    mixedMoment B raw26693step0 raw26693step0Labels = mixedMoment B raw26693step1 raw26693step1Labels := by
      have ha : raw26693step1 = (fun i j => raw26693step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26693step1 raw26693step0; decide +kernel
      have hl : raw26693step1Labels = raw26693step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26693step0 raw26693step0Labels permutation32 permutation6
    mixedMoment B raw26693step1 raw26693step1Labels = mixedMoment B raw26693step2 raw26693step2Labels := by
      have ha : raw26693step2 = raw26693step1 := by apply Matrix.ext; unfold raw26693step2 raw26693step1; decide +kernel
      have hl : raw26693step1Labels = labelEmbedding9 ∘ raw26693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26693step1 raw26693step1Labels raw26693step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw26694 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26694step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26694 raw26694Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26694 raw26694Labels = mixedMoment B raw26694step0 raw26694step0Labels := by
      have hz : ∀ j, raw26694 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26694step0 = (fun i j => raw26694 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26694step0 raw26694; decide +kernel
      have hl : raw26694step0Labels = raw26694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26694 raw26694Labels permutation265 hz
    mixedMoment B raw26694step0 raw26694step0Labels = mixedMoment B raw26694step1 raw26694step1Labels := by
      have ha : raw26694step1 = (fun i j => raw26694step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26694step1 raw26694step0; decide +kernel
      have hl : raw26694step1Labels = raw26694step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26694step0 raw26694step0Labels permutation36 permutation6
    mixedMoment B raw26694step1 raw26694step1Labels = mixedMoment B raw26694step2 raw26694step2Labels := by
      have ha : raw26694step2 = raw26694step1 := by apply Matrix.ext; unfold raw26694step2 raw26694step1; decide +kernel
      have hl : raw26694step1Labels = labelEmbedding9 ∘ raw26694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26694step1 raw26694step1Labels raw26694step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw26695 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26695step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26695 raw26695Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26695 raw26695Labels = mixedMoment B raw26695step0 raw26695step0Labels := by
      have hz : ∀ j, raw26695 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26695step0 = (fun i j => raw26695 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26695step0 raw26695; decide +kernel
      have hl : raw26695step0Labels = raw26695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26695 raw26695Labels permutation265 hz
    mixedMoment B raw26695step0 raw26695step0Labels = mixedMoment B raw26695step1 raw26695step1Labels := by
      have ha : raw26695step1 = (fun i j => raw26695step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26695step1 raw26695step0; decide +kernel
      have hl : raw26695step1Labels = raw26695step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26695step0 raw26695step0Labels permutation33 permutation6
    mixedMoment B raw26695step1 raw26695step1Labels = mixedMoment B raw26695step2 raw26695step2Labels := by
      have ha : raw26695step2 = raw26695step1 := by apply Matrix.ext; unfold raw26695step2 raw26695step1; decide +kernel
      have hl : raw26695step1Labels = labelEmbedding9 ∘ raw26695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26695step1 raw26695step1Labels raw26695step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw26696 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26696step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26696 raw26696Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26696 raw26696Labels = mixedMoment B raw26696step0 raw26696step0Labels := by
      have ha : raw26696step0 = (fun i j => raw26696 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26696step0 raw26696; decide +kernel
      have hl : raw26696step0Labels = raw26696Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26696 raw26696Labels permutation153 permutation6
    mixedMoment B raw26696step0 raw26696step0Labels = mixedMoment B raw26696step1 raw26696step1Labels := by
      have ha : raw26696step1 = raw26696step0 := by apply Matrix.ext; unfold raw26696step1 raw26696step0; decide +kernel
      have hl : raw26696step0Labels = labelEmbedding9 ∘ raw26696step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26696step0 raw26696step0Labels raw26696step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26697 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26697step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26697 raw26697Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26697 raw26697Labels = mixedMoment B raw26697step0 raw26697step0Labels := by
      have hz : ∀ j, raw26697 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26697step0 = (fun i j => raw26697 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26697step0 raw26697; decide +kernel
      have hl : raw26697step0Labels = raw26697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26697 raw26697Labels permutation265 hz
    mixedMoment B raw26697step0 raw26697step0Labels = mixedMoment B raw26697step1 raw26697step1Labels := by
      have ha : raw26697step1 = (fun i j => raw26697step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26697step1 raw26697step0; decide +kernel
      have hl : raw26697step1Labels = raw26697step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26697step0 raw26697step0Labels permutation33 permutation6
    mixedMoment B raw26697step1 raw26697step1Labels = mixedMoment B raw26697step2 raw26697step2Labels := by
      have ha : raw26697step2 = raw26697step1 := by apply Matrix.ext; unfold raw26697step2 raw26697step1; decide +kernel
      have hl : raw26697step1Labels = labelEmbedding9 ∘ raw26697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26697step1 raw26697step1Labels raw26697step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw26698 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26698step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26698 raw26698Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26698 raw26698Labels = mixedMoment B raw26698step0 raw26698step0Labels := by
      have hz : ∀ j, raw26698 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26698step0 = (fun i j => raw26698 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26698step0 raw26698; decide +kernel
      have hl : raw26698step0Labels = raw26698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26698 raw26698Labels permutation265 hz
    mixedMoment B raw26698step0 raw26698step0Labels = mixedMoment B raw26698step1 raw26698step1Labels := by
      have ha : raw26698step1 = (fun i j => raw26698step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26698step1 raw26698step0; decide +kernel
      have hl : raw26698step1Labels = raw26698step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26698step0 raw26698step0Labels permutation39 permutation6
    mixedMoment B raw26698step1 raw26698step1Labels = mixedMoment B raw26698step2 raw26698step2Labels := by
      have ha : raw26698step2 = raw26698step1 := by apply Matrix.ext; unfold raw26698step2 raw26698step1; decide +kernel
      have hl : raw26698step1Labels = labelEmbedding9 ∘ raw26698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26698step1 raw26698step1Labels raw26698step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw26699 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw26699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw26699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26699step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26699 raw26699Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26699 raw26699Labels = mixedMoment B raw26699step0 raw26699step0Labels := by
      have hz : ∀ j, raw26699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26699step0 = (fun i j => raw26699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26699step0 raw26699; decide +kernel
      have hl : raw26699step0Labels = raw26699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26699 raw26699Labels permutation265 hz
    mixedMoment B raw26699step0 raw26699step0Labels = mixedMoment B raw26699step1 raw26699step1Labels := by
      have ha : raw26699step1 = (fun i j => raw26699step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26699step1 raw26699step0; decide +kernel
      have hl : raw26699step1Labels = raw26699step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26699step0 raw26699step0Labels permutation44 permutation7
    mixedMoment B raw26699step1 raw26699step1Labels = mixedMoment B raw26699step2 raw26699step2Labels := by
      have ha : raw26699step2 = raw26699step1 := by apply Matrix.ext; unfold raw26699step2 raw26699step1; decide +kernel
      have hl : raw26699step1Labels = labelEmbedding10 ∘ raw26699step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26699step1 raw26699step1Labels raw26699step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw26700 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26700step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26700 raw26700Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26700 raw26700Labels = mixedMoment B raw26700step0 raw26700step0Labels := by
      have hz : ∀ j, raw26700 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26700step0 = (fun i j => raw26700 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26700step0 raw26700; decide +kernel
      have hl : raw26700step0Labels = raw26700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26700 raw26700Labels permutation265 hz
    mixedMoment B raw26700step0 raw26700step0Labels = mixedMoment B raw26700step1 raw26700step1Labels := by
      have ha : raw26700step1 = (fun i j => raw26700step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26700step1 raw26700step0; decide +kernel
      have hl : raw26700step1Labels = raw26700step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26700step0 raw26700step0Labels permutation50 permutation7
    mixedMoment B raw26700step1 raw26700step1Labels = mixedMoment B raw26700step2 raw26700step2Labels := by
      have ha : raw26700step2 = raw26700step1 := by apply Matrix.ext; unfold raw26700step2 raw26700step1; decide +kernel
      have hl : raw26700step1Labels = labelEmbedding10 ∘ raw26700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26700step1 raw26700step1Labels raw26700step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw26701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26701 raw26701Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw26701 raw26701Labels = mixedMoment B raw26701step0 raw26701step0Labels := by
      have ha : raw26701step0 = (fun i j => raw26701 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26701step0 raw26701; decide +kernel
      have hl : raw26701step0Labels = raw26701Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26701 raw26701Labels permutation173 permutation2
    _ = mixedMoment B node1228 node1228Labels := by rfl

def raw26702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26702 raw26702Labels = mixedMoment B node2503 node2503Labels := by
  calc
    mixedMoment B raw26702 raw26702Labels = mixedMoment B raw26702step0 raw26702step0Labels := by
      have ha : raw26702step0 = (fun i j => raw26702 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26702step0 raw26702; decide +kernel
      have hl : raw26702step0Labels = raw26702Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26702 raw26702Labels permutation173 permutation2
    _ = mixedMoment B node2503 node2503Labels := by rfl

def raw26703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26703 raw26703Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw26703 raw26703Labels = mixedMoment B raw26703step0 raw26703step0Labels := by
      have ha : raw26703step0 = (fun i j => raw26703 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26703step0 raw26703; decide +kernel
      have hl : raw26703step0Labels = raw26703Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26703 raw26703Labels permutation156 permutation2
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw26704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26704 raw26704Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw26704 raw26704Labels = mixedMoment B raw26704step0 raw26704step0Labels := by
      have ha : raw26704step0 = (fun i j => raw26704 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26704step0 raw26704; decide +kernel
      have hl : raw26704step0Labels = raw26704Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26704 raw26704Labels permutation163 permutation2
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw26705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26705 raw26705Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw26705 raw26705Labels = mixedMoment B raw26705step0 raw26705step0Labels := by
      have ha : raw26705step0 = (fun i j => raw26705 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26705step0 raw26705; decide +kernel
      have hl : raw26705step0Labels = raw26705Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26705 raw26705Labels permutation169 permutation2
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw26706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26706 raw26706Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw26706 raw26706Labels = mixedMoment B raw26706step0 raw26706step0Labels := by
      have ha : raw26706step0 = (fun i j => raw26706 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26706step0 raw26706; decide +kernel
      have hl : raw26706step0Labels = raw26706Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26706 raw26706Labels permutation173 permutation2
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw26707 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw26707Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26707step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26707step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26707 raw26707Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw26707 raw26707Labels = mixedMoment B raw26707step0 raw26707step0Labels := by
      have ha : raw26707step0 = (fun i j => raw26707 (permutation173 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26707step0 raw26707; decide +kernel
      have hl : raw26707step0Labels = raw26707Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26707 raw26707Labels permutation173 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw26708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26708 raw26708Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw26708 raw26708Labels = mixedMoment B raw26708step0 raw26708step0Labels := by
      have ha : raw26708step0 = (fun i j => raw26708 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26708step0 raw26708; decide +kernel
      have hl : raw26708step0Labels = raw26708Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26708 raw26708Labels permutation170 permutation2
    _ = mixedMoment B node5100 node5100Labels := by rfl

def raw26709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26709 raw26709Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw26709 raw26709Labels = mixedMoment B raw26709step0 raw26709step0Labels := by
      have ha : raw26709step0 = (fun i j => raw26709 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26709step0 raw26709; decide +kernel
      have hl : raw26709step0Labels = raw26709Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26709 raw26709Labels permutation168 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw26710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26710 raw26710Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw26710 raw26710Labels = mixedMoment B raw26710step0 raw26710step0Labels := by
      have hz : ∀ j, raw26710 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26710step0 = (fun i j => raw26710 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26710step0 raw26710; decide +kernel
      have hl : raw26710step0Labels = raw26710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26710 raw26710Labels permutation590 hz
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw26711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26711step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26711 raw26711Labels = mixedMoment B node4169 node4169Labels := by
  calc
    mixedMoment B raw26711 raw26711Labels = mixedMoment B raw26711step0 raw26711step0Labels := by
      have ha : raw26711step0 = (fun i j => raw26711 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26711step0 raw26711; decide +kernel
      have hl : raw26711step0Labels = raw26711Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26711 raw26711Labels permutation185 permutation3
    mixedMoment B raw26711step0 raw26711step0Labels = mixedMoment B raw26711step1 raw26711step1Labels := by
      have ha : raw26711step1 = raw26711step0 := by apply Matrix.ext; unfold raw26711step1 raw26711step0; decide +kernel
      have hl : raw26711step0Labels = labelEmbedding6 ∘ raw26711step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26711step0 raw26711step0Labels raw26711step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4169 node4169Labels := by rfl

def raw26712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26712step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26712 raw26712Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26712 raw26712Labels = mixedMoment B raw26712step0 raw26712step0Labels := by
      have ha : raw26712step0 = (fun i j => raw26712 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26712step0 raw26712; decide +kernel
      have hl : raw26712step0Labels = raw26712Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26712 raw26712Labels permutation185 permutation3
    mixedMoment B raw26712step0 raw26712step0Labels = mixedMoment B raw26712step1 raw26712step1Labels := by
      have ha : raw26712step1 = raw26712step0 := by apply Matrix.ext; unfold raw26712step1 raw26712step0; decide +kernel
      have hl : raw26712step0Labels = labelEmbedding6 ∘ raw26712step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26712step0 raw26712step0Labels raw26712step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26713step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26713 raw26713Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26713 raw26713Labels = mixedMoment B raw26713step0 raw26713step0Labels := by
      have ha : raw26713step0 = (fun i j => raw26713 (permutation209 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26713step0 raw26713; decide +kernel
      have hl : raw26713step0Labels = raw26713Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26713 raw26713Labels permutation209 permutation3
    mixedMoment B raw26713step0 raw26713step0Labels = mixedMoment B raw26713step1 raw26713step1Labels := by
      have ha : raw26713step1 = raw26713step0 := by apply Matrix.ext; unfold raw26713step1 raw26713step0; decide +kernel
      have hl : raw26713step0Labels = labelEmbedding6 ∘ raw26713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26713step0 raw26713step0Labels raw26713step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26714step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26714 raw26714Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26714 raw26714Labels = mixedMoment B raw26714step0 raw26714step0Labels := by
      have ha : raw26714step0 = (fun i j => raw26714 (permutation233 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26714step0 raw26714; decide +kernel
      have hl : raw26714step0Labels = raw26714Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26714 raw26714Labels permutation233 permutation3
    mixedMoment B raw26714step0 raw26714step0Labels = mixedMoment B raw26714step1 raw26714step1Labels := by
      have ha : raw26714step1 = raw26714step0 := by apply Matrix.ext; unfold raw26714step1 raw26714step0; decide +kernel
      have hl : raw26714step0Labels = labelEmbedding6 ∘ raw26714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26714step0 raw26714step0Labels raw26714step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw26715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26715 raw26715Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26715 raw26715Labels = mixedMoment B raw26715step0 raw26715step0Labels := by
      have hz : ∀ j, raw26715 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26715step0 = (fun i j => raw26715 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26715step0 raw26715; decide +kernel
      have hl : raw26715step0Labels = raw26715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26715 raw26715Labels permutation590 hz
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw26716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26716step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26716 raw26716Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw26716 raw26716Labels = mixedMoment B raw26716step0 raw26716step0Labels := by
      have ha : raw26716step0 = (fun i j => raw26716 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26716step0 raw26716; decide +kernel
      have hl : raw26716step0Labels = raw26716Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26716 raw26716Labels permutation161 permutation3
    mixedMoment B raw26716step0 raw26716step0Labels = mixedMoment B raw26716step1 raw26716step1Labels := by
      have ha : raw26716step1 = raw26716step0 := by apply Matrix.ext; unfold raw26716step1 raw26716step0; decide +kernel
      have hl : raw26716step0Labels = labelEmbedding6 ∘ raw26716step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26716step0 raw26716step0Labels raw26716step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4150 node4150Labels := by rfl

def raw26717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26717 raw26717Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw26717 raw26717Labels = mixedMoment B raw26717step0 raw26717step0Labels := by
      have ha : raw26717step0 = (fun i j => raw26717 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26717step0 raw26717; decide +kernel
      have hl : raw26717step0Labels = raw26717Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26717 raw26717Labels permutation173 permutation2
    _ = mixedMoment B node4544 node4544Labels := by rfl

def raw26718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26718 raw26718Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26718 raw26718Labels = mixedMoment B raw26718step0 raw26718step0Labels := by
      have ha : raw26718step0 = (fun i j => raw26718 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26718step0 raw26718; decide +kernel
      have hl : raw26718step0Labels = raw26718Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26718 raw26718Labels permutation163 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw26719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26719 raw26719Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26719 raw26719Labels = mixedMoment B raw26719step0 raw26719step0Labels := by
      have ha : raw26719step0 = (fun i j => raw26719 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26719step0 raw26719; decide +kernel
      have hl : raw26719step0Labels = raw26719Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26719 raw26719Labels permutation169 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw26720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26720 raw26720Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26720 raw26720Labels = mixedMoment B raw26720step0 raw26720step0Labels := by
      have hz : ∀ j, raw26720 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26720step0 = (fun i j => raw26720 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26720step0 raw26720; decide +kernel
      have hl : raw26720step0Labels = raw26720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26720 raw26720Labels permutation590 hz
    mixedMoment B raw26720step0 raw26720step0Labels = mixedMoment B raw26720step1 raw26720step1Labels := by
      have ha : raw26720step1 = (fun i j => raw26720step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26720step1 raw26720step0; decide +kernel
      have hl : raw26720step1Labels = raw26720step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26720step0 raw26720step0Labels permutation35 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw26721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26721step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26721 raw26721Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw26721 raw26721Labels = mixedMoment B raw26721step0 raw26721step0Labels := by
      have ha : raw26721step0 = (fun i j => raw26721 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26721step0 raw26721; decide +kernel
      have hl : raw26721step0Labels = raw26721Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26721 raw26721Labels permutation155 permutation3
    mixedMoment B raw26721step0 raw26721step0Labels = mixedMoment B raw26721step1 raw26721step1Labels := by
      have ha : raw26721step1 = raw26721step0 := by apply Matrix.ext; unfold raw26721step1 raw26721step0; decide +kernel
      have hl : raw26721step0Labels = labelEmbedding6 ∘ raw26721step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26721step0 raw26721step0Labels raw26721step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4150 node4150Labels := by rfl

def raw26722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26722 raw26722Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw26722 raw26722Labels = mixedMoment B raw26722step0 raw26722step0Labels := by
      have ha : raw26722step0 = (fun i j => raw26722 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26722step0 raw26722; decide +kernel
      have hl : raw26722step0Labels = raw26722Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26722 raw26722Labels permutation171 permutation2
    _ = mixedMoment B node4544 node4544Labels := by rfl

def raw26723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26723 raw26723Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26723 raw26723Labels = mixedMoment B raw26723step0 raw26723step0Labels := by
      have ha : raw26723step0 = (fun i j => raw26723 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26723step0 raw26723; decide +kernel
      have hl : raw26723step0Labels = raw26723Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26723 raw26723Labels permutation157 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw26724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26724 raw26724Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26724 raw26724Labels = mixedMoment B raw26724step0 raw26724step0Labels := by
      have ha : raw26724step0 = (fun i j => raw26724 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26724step0 raw26724; decide +kernel
      have hl : raw26724step0Labels = raw26724Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26724 raw26724Labels permutation168 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw26725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26725 raw26725Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26725 raw26725Labels = mixedMoment B raw26725step0 raw26725step0Labels := by
      have hz : ∀ j, raw26725 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26725step0 = (fun i j => raw26725 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26725step0 raw26725; decide +kernel
      have hl : raw26725step0Labels = raw26725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26725 raw26725Labels permutation590 hz
    mixedMoment B raw26725step0 raw26725step0Labels = mixedMoment B raw26725step1 raw26725step1Labels := by
      have ha : raw26725step1 = (fun i j => raw26725step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26725step1 raw26725step0; decide +kernel
      have hl : raw26725step1Labels = raw26725step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26725step0 raw26725step0Labels permutation33 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw26726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26726step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26726 raw26726Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw26726 raw26726Labels = mixedMoment B raw26726step0 raw26726step0Labels := by
      have ha : raw26726step0 = (fun i j => raw26726 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26726step0 raw26726; decide +kernel
      have hl : raw26726step0Labels = raw26726Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26726 raw26726Labels permutation153 permutation3
    mixedMoment B raw26726step0 raw26726step0Labels = mixedMoment B raw26726step1 raw26726step1Labels := by
      have ha : raw26726step1 = raw26726step0 := by apply Matrix.ext; unfold raw26726step1 raw26726step0; decide +kernel
      have hl : raw26726step0Labels = labelEmbedding6 ∘ raw26726step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26726step0 raw26726step0Labels raw26726step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4150 node4150Labels := by rfl

def raw26727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26727 raw26727Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw26727 raw26727Labels = mixedMoment B raw26727step0 raw26727step0Labels := by
      have ha : raw26727step0 = (fun i j => raw26727 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26727step0 raw26727; decide +kernel
      have hl : raw26727step0Labels = raw26727Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26727 raw26727Labels permutation170 permutation2
    _ = mixedMoment B node4544 node4544Labels := by rfl

def raw26728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26728 raw26728Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26728 raw26728Labels = mixedMoment B raw26728step0 raw26728step0Labels := by
      have ha : raw26728step0 = (fun i j => raw26728 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26728step0 raw26728; decide +kernel
      have hl : raw26728step0Labels = raw26728Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26728 raw26728Labels permutation156 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw26729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26729 raw26729Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26729 raw26729Labels = mixedMoment B raw26729step0 raw26729step0Labels := by
      have ha : raw26729step0 = (fun i j => raw26729 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26729step0 raw26729; decide +kernel
      have hl : raw26729step0Labels = raw26729Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26729 raw26729Labels permutation162 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw26730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw26730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26730 raw26730Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26730 raw26730Labels = mixedMoment B raw26730step0 raw26730step0Labels := by
      have hz : ∀ j, raw26730 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26730step0 = (fun i j => raw26730 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26730step0 raw26730; decide +kernel
      have hl : raw26730step0Labels = raw26730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26730 raw26730Labels permutation590 hz
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw26731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26731step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26731 raw26731Labels = mixedMoment B node4149 node4149Labels := by
  calc
    mixedMoment B raw26731 raw26731Labels = mixedMoment B raw26731step0 raw26731step0Labels := by
      have ha : raw26731step0 = (fun i j => raw26731 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26731step0 raw26731; decide +kernel
      have hl : raw26731step0Labels = raw26731Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26731 raw26731Labels permutation152 permutation3
    mixedMoment B raw26731step0 raw26731step0Labels = mixedMoment B raw26731step1 raw26731step1Labels := by
      have ha : raw26731step1 = raw26731step0 := by apply Matrix.ext; unfold raw26731step1 raw26731step0; decide +kernel
      have hl : raw26731step0Labels = labelEmbedding6 ∘ raw26731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26731step0 raw26731step0Labels raw26731step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4149 node4149Labels := by rfl

def raw26732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26732 raw26732Labels = mixedMoment B node4550 node4550Labels := by
  calc
    _ = mixedMoment B node4550 node4550Labels := by rfl

def raw26733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26733step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26733step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26733 raw26733Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw26733 raw26733Labels = mixedMoment B raw26733step0 raw26733step0Labels := by
      have ha : raw26733step0 = (fun i j => raw26733 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26733step0 raw26733; decide +kernel
      have hl : raw26733step0Labels = raw26733Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26733 raw26733Labels permutation224 permutation3
    mixedMoment B raw26733step0 raw26733step0Labels = mixedMoment B raw26733step1 raw26733step1Labels := by
      have ha : raw26733step1 = raw26733step0 := by apply Matrix.ext; unfold raw26733step1 raw26733step0; decide +kernel
      have hl : raw26733step0Labels = labelEmbedding6 ∘ raw26733step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26733step0 raw26733step0Labels raw26733step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw26734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26734 raw26734Labels = mixedMoment B node2999 node2999Labels := by
  calc
    mixedMoment B raw26734 raw26734Labels = mixedMoment B raw26734step0 raw26734step0Labels := by
      have ha : raw26734step0 = (fun i j => raw26734 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26734step0 raw26734; decide +kernel
      have hl : raw26734step0Labels = raw26734Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26734 raw26734Labels permutation152 permutation3
    _ = mixedMoment B node2999 node2999Labels := by rfl

def raw26735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26735 raw26735Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw26735 raw26735Labels = mixedMoment B raw26735step0 raw26735step0Labels := by
      have ha : raw26735step0 = (fun i j => raw26735 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26735step0 raw26735; decide +kernel
      have hl : raw26735step0Labels = raw26735Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26735 raw26735Labels permutation224 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw26736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw26736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26736 raw26736Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw26736 raw26736Labels = mixedMoment B raw26736step0 raw26736step0Labels := by
      have hz : ∀ j, raw26736 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26736step0 = (fun i j => raw26736 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26736step0 raw26736; decide +kernel
      have hl : raw26736step0Labels = raw26736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26736 raw26736Labels permutation590 hz
    mixedMoment B raw26736step0 raw26736step0Labels = mixedMoment B raw26736step1 raw26736step1Labels := by
      have ha : raw26736step1 = (fun i j => raw26736step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26736step1 raw26736step0; decide +kernel
      have hl : raw26736step1Labels = raw26736step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26736step0 raw26736step0Labels permutation32 permutation3
    _ = mixedMoment B node3111 node3111Labels := by rfl

def raw26737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26737 raw26737Labels = mixedMoment B node597 node597Labels := by
  calc
    mixedMoment B raw26737 raw26737Labels = mixedMoment B raw26737step0 raw26737step0Labels := by
      have ha : raw26737step0 = (fun i j => raw26737 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26737step0 raw26737; decide +kernel
      have hl : raw26737step0Labels = raw26737Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26737 raw26737Labels permutation185 permutation3
    _ = mixedMoment B node597 node597Labels := by rfl

def raw26738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26738 raw26738Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw26738 raw26738Labels = mixedMoment B raw26738step0 raw26738step0Labels := by
      have ha : raw26738step0 = (fun i j => raw26738 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26738step0 raw26738; decide +kernel
      have hl : raw26738step0Labels = raw26738Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26738 raw26738Labels permutation185 permutation3
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw26739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26739 raw26739Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw26739 raw26739Labels = mixedMoment B raw26739step0 raw26739step0Labels := by
      have ha : raw26739step0 = (fun i j => raw26739 (permutation209 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26739step0 raw26739; decide +kernel
      have hl : raw26739step0Labels = raw26739Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26739 raw26739Labels permutation209 permutation3
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw26740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26740 raw26740Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw26740 raw26740Labels = mixedMoment B raw26740step0 raw26740step0Labels := by
      have ha : raw26740step0 = (fun i j => raw26740 (permutation233 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26740step0 raw26740; decide +kernel
      have hl : raw26740step0Labels = raw26740Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26740 raw26740Labels permutation233 permutation3
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw26741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26741step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26741 raw26741Labels = mixedMoment B node1298 node1298Labels := by
  calc
    mixedMoment B raw26741 raw26741Labels = mixedMoment B raw26741step0 raw26741step0Labels := by
      have hz : ∀ j, raw26741 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26741step0 = (fun i j => raw26741 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26741step0 raw26741; decide +kernel
      have hl : raw26741step0Labels = raw26741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26741 raw26741Labels permutation590 hz
    mixedMoment B raw26741step0 raw26741step0Labels = mixedMoment B raw26741step1 raw26741step1Labels := by
      have ha : raw26741step1 = (fun i j => raw26741step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26741step1 raw26741step0; decide +kernel
      have hl : raw26741step1Labels = raw26741step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26741step0 raw26741step0Labels permutation41 permutation3
    _ = mixedMoment B node1298 node1298Labels := by rfl

def raw26742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26742 raw26742Labels = mixedMoment B node578 node578Labels := by
  calc
    mixedMoment B raw26742 raw26742Labels = mixedMoment B raw26742step0 raw26742step0Labels := by
      have ha : raw26742step0 = (fun i j => raw26742 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26742step0 raw26742; decide +kernel
      have hl : raw26742step0Labels = raw26742Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26742 raw26742Labels permutation161 permutation3
    _ = mixedMoment B node578 node578Labels := by rfl

def raw26743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26743 raw26743Labels = mixedMoment B node1162 node1162Labels := by
  calc
    mixedMoment B raw26743 raw26743Labels = mixedMoment B raw26743step0 raw26743step0Labels := by
      have ha : raw26743step0 = (fun i j => raw26743 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26743step0 raw26743; decide +kernel
      have hl : raw26743step0Labels = raw26743Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26743 raw26743Labels permutation161 permutation3
    _ = mixedMoment B node1162 node1162Labels := by rfl

def raw26744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26744 raw26744Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw26744 raw26744Labels = mixedMoment B raw26744step0 raw26744step0Labels := by
      have ha : raw26744step0 = (fun i j => raw26744 (permutation203 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26744step0 raw26744; decide +kernel
      have hl : raw26744step0Labels = raw26744Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26744 raw26744Labels permutation203 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw26745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26745 raw26745Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw26745 raw26745Labels = mixedMoment B raw26745step0 raw26745step0Labels := by
      have ha : raw26745step0 = (fun i j => raw26745 (permutation227 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26745step0 raw26745; decide +kernel
      have hl : raw26745step0Labels = raw26745Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26745 raw26745Labels permutation227 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw26746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26746step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26746 raw26746Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw26746 raw26746Labels = mixedMoment B raw26746step0 raw26746step0Labels := by
      have hz : ∀ j, raw26746 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26746step0 = (fun i j => raw26746 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26746step0 raw26746; decide +kernel
      have hl : raw26746step0Labels = raw26746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26746 raw26746Labels permutation590 hz
    mixedMoment B raw26746step0 raw26746step0Labels = mixedMoment B raw26746step1 raw26746step1Labels := by
      have ha : raw26746step1 = (fun i j => raw26746step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26746step1 raw26746step0; decide +kernel
      have hl : raw26746step1Labels = raw26746step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26746step0 raw26746step0Labels permutation35 permutation3
    _ = mixedMoment B node1266 node1266Labels := by rfl

def raw26747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26747 raw26747Labels = mixedMoment B node578 node578Labels := by
  calc
    mixedMoment B raw26747 raw26747Labels = mixedMoment B raw26747step0 raw26747step0Labels := by
      have ha : raw26747step0 = (fun i j => raw26747 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26747step0 raw26747; decide +kernel
      have hl : raw26747step0Labels = raw26747Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26747 raw26747Labels permutation155 permutation3
    _ = mixedMoment B node578 node578Labels := by rfl

def raw26748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26748 raw26748Labels = mixedMoment B node1162 node1162Labels := by
  calc
    mixedMoment B raw26748 raw26748Labels = mixedMoment B raw26748step0 raw26748step0Labels := by
      have ha : raw26748step0 = (fun i j => raw26748 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26748step0 raw26748; decide +kernel
      have hl : raw26748step0Labels = raw26748Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26748 raw26748Labels permutation155 permutation3
    _ = mixedMoment B node1162 node1162Labels := by rfl

def raw26749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26749 raw26749Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw26749 raw26749Labels = mixedMoment B raw26749step0 raw26749step0Labels := by
      have ha : raw26749step0 = (fun i j => raw26749 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26749step0 raw26749; decide +kernel
      have hl : raw26749step0Labels = raw26749Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26749 raw26749Labels permutation179 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw26750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26750 raw26750Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw26750 raw26750Labels = mixedMoment B raw26750step0 raw26750step0Labels := by
      have ha : raw26750step0 = (fun i j => raw26750 (permutation225 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26750step0 raw26750; decide +kernel
      have hl : raw26750step0Labels = raw26750Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26750 raw26750Labels permutation225 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw26751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26751step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26751 raw26751Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw26751 raw26751Labels = mixedMoment B raw26751step0 raw26751step0Labels := by
      have hz : ∀ j, raw26751 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26751step0 = (fun i j => raw26751 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26751step0 raw26751; decide +kernel
      have hl : raw26751step0Labels = raw26751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26751 raw26751Labels permutation590 hz
    mixedMoment B raw26751step0 raw26751step0Labels = mixedMoment B raw26751step1 raw26751step1Labels := by
      have ha : raw26751step1 = (fun i j => raw26751step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26751step1 raw26751step0; decide +kernel
      have hl : raw26751step1Labels = raw26751step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26751step0 raw26751step0Labels permutation33 permutation3
    _ = mixedMoment B node1266 node1266Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
