import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24448 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24448 raw24448Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw24448 raw24448Labels = mixedMoment B raw24448step0 raw24448step0Labels := by
      have hz : ∀ j, raw24448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24448step0 = (fun i j => raw24448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24448step0 raw24448; decide +kernel
      have hl : raw24448step0Labels = raw24448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24448 raw24448Labels permutation346 hz
    mixedMoment B raw24448step0 raw24448step0Labels = mixedMoment B raw24448step1 raw24448step1Labels := by
      have ha : raw24448step1 = (fun i j => raw24448step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24448step1 raw24448step0; decide +kernel
      have hl : raw24448step1Labels = raw24448step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24448step0 raw24448step0Labels permutation34 permutation7
    mixedMoment B raw24448step1 raw24448step1Labels = mixedMoment B raw24448step2 raw24448step2Labels := by
      have ha : raw24448step2 = raw24448step1 := by apply Matrix.ext; unfold raw24448step2 raw24448step1; decide +kernel
      have hl : raw24448step1Labels = labelEmbedding1 ∘ raw24448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24448step1 raw24448step1Labels raw24448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw24449 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24449 raw24449Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw24449 raw24449Labels = mixedMoment B raw24449step0 raw24449step0Labels := by
      have hz : ∀ j, raw24449 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24449step0 = (fun i j => raw24449 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24449step0 raw24449; decide +kernel
      have hl : raw24449step0Labels = raw24449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24449 raw24449Labels permutation265 hz
    mixedMoment B raw24449step0 raw24449step0Labels = mixedMoment B raw24449step1 raw24449step1Labels := by
      have ha : raw24449step1 = (fun i j => raw24449step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24449step1 raw24449step0; decide +kernel
      have hl : raw24449step1Labels = raw24449step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24449step0 raw24449step0Labels permutation34 permutation7
    mixedMoment B raw24449step1 raw24449step1Labels = mixedMoment B raw24449step2 raw24449step2Labels := by
      have ha : raw24449step2 = raw24449step1 := by apply Matrix.ext; unfold raw24449step2 raw24449step1; decide +kernel
      have hl : raw24449step1Labels = labelEmbedding1 ∘ raw24449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24449step1 raw24449step1Labels raw24449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw24450 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24450step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24450 raw24450Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw24450 raw24450Labels = mixedMoment B raw24450step0 raw24450step0Labels := by
      have hz : ∀ j, raw24450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24450step0 = (fun i j => raw24450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24450step0 raw24450; decide +kernel
      have hl : raw24450step0Labels = raw24450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24450 raw24450Labels permutation346 hz
    mixedMoment B raw24450step0 raw24450step0Labels = mixedMoment B raw24450step1 raw24450step1Labels := by
      have hz : ∀ j, raw24450step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24450step1 = (fun i j => raw24450step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24450step1 raw24450step0; decide +kernel
      have hl : raw24450step1Labels = raw24450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24450step0 raw24450step0Labels permutation56 hz
    mixedMoment B raw24450step1 raw24450step1Labels = mixedMoment B raw24450step2 raw24450step2Labels := by
      have ha : raw24450step2 = (fun i j => raw24450step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24450step2 raw24450step1; decide +kernel
      have hl : raw24450step2Labels = raw24450step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24450step1 raw24450step1Labels permutation10 permutation7
    mixedMoment B raw24450step2 raw24450step2Labels = mixedMoment B raw24450step3 raw24450step3Labels := by
      have ha : raw24450step3 = raw24450step2 := by apply Matrix.ext; unfold raw24450step3 raw24450step2; decide +kernel
      have hl : raw24450step2Labels = labelEmbedding1 ∘ raw24450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24450step2 raw24450step2Labels raw24450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1295 node1295Labels := by rfl

def raw24451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24451 raw24451Labels = mixedMoment B node1287 node1287Labels := by
  calc
    mixedMoment B raw24451 raw24451Labels = mixedMoment B raw24451step0 raw24451step0Labels := by
      have hz : ∀ j, raw24451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24451step0 = (fun i j => raw24451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24451step0 raw24451; decide +kernel
      have hl : raw24451step0Labels = raw24451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24451 raw24451Labels permutation346 hz
    mixedMoment B raw24451step0 raw24451step0Labels = mixedMoment B raw24451step1 raw24451step1Labels := by
      have hz : ∀ j, raw24451step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24451step1 = (fun i j => raw24451step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24451step1 raw24451step0; decide +kernel
      have hl : raw24451step1Labels = raw24451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24451step0 raw24451step0Labels permutation56 hz
    mixedMoment B raw24451step1 raw24451step1Labels = mixedMoment B raw24451step2 raw24451step2Labels := by
      have ha : raw24451step2 = (fun i j => raw24451step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24451step2 raw24451step1; decide +kernel
      have hl : raw24451step2Labels = raw24451step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24451step1 raw24451step1Labels permutation10 permutation2
    _ = mixedMoment B node1287 node1287Labels := by rfl

def raw24452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24452 raw24452Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw24452 raw24452Labels = mixedMoment B raw24452step0 raw24452step0Labels := by
      have hz : ∀ j, raw24452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24452step0 = (fun i j => raw24452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24452step0 raw24452; decide +kernel
      have hl : raw24452step0Labels = raw24452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24452 raw24452Labels permutation346 hz
    mixedMoment B raw24452step0 raw24452step0Labels = mixedMoment B raw24452step1 raw24452step1Labels := by
      have ha : raw24452step1 = (fun i j => raw24452step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24452step1 raw24452step0; decide +kernel
      have hl : raw24452step1Labels = raw24452step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24452step0 raw24452step0Labels permutation34 permutation2
    _ = mixedMoment B node2584 node2584Labels := by rfl

def raw24453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24453 raw24453Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw24453 raw24453Labels = mixedMoment B raw24453step0 raw24453step0Labels := by
      have hz : ∀ j, raw24453 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24453step0 = (fun i j => raw24453 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24453step0 raw24453; decide +kernel
      have hl : raw24453step0Labels = raw24453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24453 raw24453Labels permutation265 hz
    mixedMoment B raw24453step0 raw24453step0Labels = mixedMoment B raw24453step1 raw24453step1Labels := by
      have ha : raw24453step1 = (fun i j => raw24453step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24453step1 raw24453step0; decide +kernel
      have hl : raw24453step1Labels = raw24453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24453step0 raw24453step0Labels permutation34 permutation2
    _ = mixedMoment B node2584 node2584Labels := by rfl

def raw24454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24454 raw24454Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw24454 raw24454Labels = mixedMoment B raw24454step0 raw24454step0Labels := by
      have hz : ∀ j, raw24454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24454step0 = (fun i j => raw24454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24454step0 raw24454; decide +kernel
      have hl : raw24454step0Labels = raw24454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24454 raw24454Labels permutation346 hz
    mixedMoment B raw24454step0 raw24454step0Labels = mixedMoment B raw24454step1 raw24454step1Labels := by
      have hz : ∀ j, raw24454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24454step1 = (fun i j => raw24454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24454step1 raw24454step0; decide +kernel
      have hl : raw24454step1Labels = raw24454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24454step0 raw24454step0Labels permutation56 hz
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw24455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -2, 2], ![2, 1, -3]]
def raw24455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -2, 2], ![2, 1, -3]]
def raw24455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -2, 2], ![2, 1, -3]]
def raw24455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24455 raw24455Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw24455 raw24455Labels = mixedMoment B raw24455step0 raw24455step0Labels := by
      have hz : ∀ j, raw24455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24455step0 = (fun i j => raw24455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24455step0 raw24455; decide +kernel
      have hl : raw24455step0Labels = raw24455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24455 raw24455Labels permutation346 hz
    mixedMoment B raw24455step0 raw24455step0Labels = mixedMoment B raw24455step1 raw24455step1Labels := by
      have hz : ∀ j, raw24455step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24455step1 = (fun i j => raw24455step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24455step1 raw24455step0; decide +kernel
      have hl : raw24455step1Labels = raw24455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24455step0 raw24455step0Labels permutation56 hz
    mixedMoment B raw24455step1 raw24455step1Labels = mixedMoment B raw24455step2 raw24455step2Labels := by
      have ha : raw24455step2 = (fun i j => raw24455step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24455step2 raw24455step1; decide +kernel
      have hl : raw24455step2Labels = raw24455step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24455step1 raw24455step1Labels permutation10 permutation2
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw24456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![1, 2, -3]]
def raw24456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![1, 2, -3]]
def raw24456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -3, 2], ![1, 2, -3]]
def raw24456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw24456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24456 raw24456Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw24456 raw24456Labels = mixedMoment B raw24456step0 raw24456step0Labels := by
      have hz : ∀ j, raw24456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24456step0 = (fun i j => raw24456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24456step0 raw24456; decide +kernel
      have hl : raw24456step0Labels = raw24456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24456 raw24456Labels permutation346 hz
    mixedMoment B raw24456step0 raw24456step0Labels = mixedMoment B raw24456step1 raw24456step1Labels := by
      have hz : ∀ j, raw24456step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24456step1 = (fun i j => raw24456step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24456step1 raw24456step0; decide +kernel
      have hl : raw24456step1Labels = raw24456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24456step0 raw24456step0Labels permutation56 hz
    mixedMoment B raw24456step1 raw24456step1Labels = mixedMoment B raw24456step2 raw24456step2Labels := by
      have ha : raw24456step2 = (fun i j => raw24456step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24456step2 raw24456step1; decide +kernel
      have hl : raw24456step2Labels = raw24456step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24456step1 raw24456step1Labels permutation22 permutation4
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw24457 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![-2, 2], ![3, -3]]
def raw24457Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24457step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![3, -3]]
def raw24457step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24457step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw24457step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24457step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw24457step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24457step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw24457step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24457 raw24457Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw24457 raw24457Labels = mixedMoment B raw24457step0 raw24457step0Labels := by
      have hz : ∀ j, raw24457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24457step0 = (fun i j => raw24457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24457step0 raw24457; decide +kernel
      have hl : raw24457step0Labels = raw24457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24457 raw24457Labels permutation346 hz
    mixedMoment B raw24457step0 raw24457step0Labels = mixedMoment B raw24457step1 raw24457step1Labels := by
      have hz : ∀ j, raw24457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24457step1 = (fun i j => raw24457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24457step1 raw24457step0; decide +kernel
      have hl : raw24457step1Labels = raw24457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24457step0 raw24457step0Labels permutation56 hz
    mixedMoment B raw24457step1 raw24457step1Labels = mixedMoment B raw24457step2 raw24457step2Labels := by
      have ha : raw24457step2 = (fun i j => raw24457step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24457step2 raw24457step1; decide +kernel
      have hl : raw24457step2Labels = raw24457step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24457step1 raw24457step1Labels permutation28 permutation0
    mixedMoment B raw24457step2 raw24457step2Labels = mixedMoment B raw24457step3 raw24457step3Labels := by
      have ha : raw24457step3 = -raw24457step2 := by apply Matrix.ext; change ∀ i j, raw24457step3 i j = -(raw24457step2 i j); unfold raw24457step3 raw24457step2; decide +kernel
      have hl : raw24457step3Labels = raw24457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw24458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24458 raw24458Labels = mixedMoment B node1230 node1230Labels := by
  calc
    mixedMoment B raw24458 raw24458Labels = mixedMoment B raw24458step0 raw24458step0Labels := by
      have hz : ∀ j, raw24458 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24458step0 = (fun i j => raw24458 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24458step0 raw24458; decide +kernel
      have hl : raw24458step0Labels = raw24458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24458 raw24458Labels permutation265 hz
    mixedMoment B raw24458step0 raw24458step0Labels = mixedMoment B raw24458step1 raw24458step1Labels := by
      have ha : raw24458step1 = (fun i j => raw24458step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24458step1 raw24458step0; decide +kernel
      have hl : raw24458step1Labels = raw24458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24458step0 raw24458step0Labels permutation34 permutation2
    _ = mixedMoment B node1230 node1230Labels := by rfl

def raw24459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24459 raw24459Labels = mixedMoment B node2551 node2551Labels := by
  calc
    mixedMoment B raw24459 raw24459Labels = mixedMoment B raw24459step0 raw24459step0Labels := by
      have ha : raw24459step0 = (fun i j => raw24459 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24459step0 raw24459; decide +kernel
      have hl : raw24459step0Labels = raw24459Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24459 raw24459Labels permutation154 permutation2
    _ = mixedMoment B node2551 node2551Labels := by rfl

def raw24460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24460 raw24460Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw24460 raw24460Labels = mixedMoment B raw24460step0 raw24460step0Labels := by
      have hz : ∀ j, raw24460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24460step0 = (fun i j => raw24460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24460step0 raw24460; decide +kernel
      have hl : raw24460step0Labels = raw24460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24460 raw24460Labels permutation265 hz
    mixedMoment B raw24460step0 raw24460step0Labels = mixedMoment B raw24460step1 raw24460step1Labels := by
      have ha : raw24460step1 = (fun i j => raw24460step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24460step1 raw24460step0; decide +kernel
      have hl : raw24460step1Labels = raw24460step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24460step0 raw24460step0Labels permutation34 permutation2
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw24461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw24461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24461 raw24461Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw24461 raw24461Labels = mixedMoment B raw24461step0 raw24461step0Labels := by
      have hz : ∀ j, raw24461 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24461step0 = (fun i j => raw24461 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24461step0 raw24461; decide +kernel
      have hl : raw24461step0Labels = raw24461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24461 raw24461Labels permutation265 hz
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw24462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw24462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw24462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24462 raw24462Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw24462 raw24462Labels = mixedMoment B raw24462step0 raw24462step0Labels := by
      have hz : ∀ j, raw24462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24462step0 = (fun i j => raw24462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24462step0 raw24462; decide +kernel
      have hl : raw24462step0Labels = raw24462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24462 raw24462Labels permutation265 hz
    mixedMoment B raw24462step0 raw24462step0Labels = mixedMoment B raw24462step1 raw24462step1Labels := by
      have ha : raw24462step1 = (fun i j => raw24462step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24462step1 raw24462step0; decide +kernel
      have hl : raw24462step1Labels = raw24462step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24462step0 raw24462step0Labels permutation34 permutation2
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw24463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw24463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw24463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw24463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24463 raw24463Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw24463 raw24463Labels = mixedMoment B raw24463step0 raw24463step0Labels := by
      have hz : ∀ j, raw24463 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24463step0 = (fun i j => raw24463 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24463step0 raw24463; decide +kernel
      have hl : raw24463step0Labels = raw24463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24463 raw24463Labels permutation265 hz
    mixedMoment B raw24463step0 raw24463step0Labels = mixedMoment B raw24463step1 raw24463step1Labels := by
      have ha : raw24463step1 = (fun i j => raw24463step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24463step1 raw24463step0; decide +kernel
      have hl : raw24463step1Labels = raw24463step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24463step0 raw24463step0Labels permutation34 permutation2
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw24464 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![-1, 1], ![2, -2]]
def raw24464Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24464step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![-1, 1], ![2, -2]]
def raw24464step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24464step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw24464step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24464step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw24464step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24464 raw24464Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw24464 raw24464Labels = mixedMoment B raw24464step0 raw24464step0Labels := by
      have hz : ∀ j, raw24464 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24464step0 = (fun i j => raw24464 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24464step0 raw24464; decide +kernel
      have hl : raw24464step0Labels = raw24464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24464 raw24464Labels permutation265 hz
    mixedMoment B raw24464step0 raw24464step0Labels = mixedMoment B raw24464step1 raw24464step1Labels := by
      have ha : raw24464step1 = (fun i j => raw24464step0 (permutation101 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24464step1 raw24464step0; decide +kernel
      have hl : raw24464step1Labels = raw24464step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24464step0 raw24464step0Labels permutation101 permutation0
    mixedMoment B raw24464step1 raw24464step1Labels = mixedMoment B raw24464step2 raw24464step2Labels := by
      have ha : raw24464step2 = -raw24464step1 := by apply Matrix.ext; change ∀ i j, raw24464step2 i j = -(raw24464step1 i j); unfold raw24464step2 raw24464step1; decide +kernel
      have hl : raw24464step2Labels = raw24464step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw24465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24465step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24465 raw24465Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw24465 raw24465Labels = mixedMoment B raw24465step0 raw24465step0Labels := by
      have ha : raw24465step0 = (fun i j => raw24465 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24465step0 raw24465; decide +kernel
      have hl : raw24465step0Labels = raw24465Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24465 raw24465Labels permutation184 permutation3
    mixedMoment B raw24465step0 raw24465step0Labels = mixedMoment B raw24465step1 raw24465step1Labels := by
      have ha : raw24465step1 = raw24465step0 := by apply Matrix.ext; unfold raw24465step1 raw24465step0; decide +kernel
      have hl : raw24465step0Labels = labelEmbedding6 ∘ raw24465step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24465step0 raw24465step0Labels raw24465step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4150 node4150Labels := by rfl

def raw24466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24466 raw24466Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw24466 raw24466Labels = mixedMoment B raw24466step0 raw24466step0Labels := by
      have ha : raw24466step0 = (fun i j => raw24466 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24466step0 raw24466; decide +kernel
      have hl : raw24466step0Labels = raw24466Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24466 raw24466Labels permutation176 permutation2
    _ = mixedMoment B node4544 node4544Labels := by rfl

def raw24467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24467 raw24467Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw24467 raw24467Labels = mixedMoment B raw24467step0 raw24467step0Labels := by
      have ha : raw24467step0 = (fun i j => raw24467 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24467step0 raw24467; decide +kernel
      have hl : raw24467step0Labels = raw24467Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24467 raw24467Labels permutation182 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw24468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24468 raw24468Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw24468 raw24468Labels = mixedMoment B raw24468step0 raw24468step0Labels := by
      have ha : raw24468step0 = (fun i j => raw24468 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24468step0 raw24468; decide +kernel
      have hl : raw24468step0Labels = raw24468Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24468 raw24468Labels permutation188 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw24469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24469step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24469step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24469 raw24469Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw24469 raw24469Labels = mixedMoment B raw24469step0 raw24469step0Labels := by
      have hz : ∀ j, raw24469 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24469step0 = (fun i j => raw24469 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24469step0 raw24469; decide +kernel
      have hl : raw24469step0Labels = raw24469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24469 raw24469Labels permutation265 hz
    mixedMoment B raw24469step0 raw24469step0Labels = mixedMoment B raw24469step1 raw24469step1Labels := by
      have ha : raw24469step1 = (fun i j => raw24469step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24469step1 raw24469step0; decide +kernel
      have hl : raw24469step1Labels = raw24469step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24469step0 raw24469step0Labels permutation40 permutation3
    mixedMoment B raw24469step1 raw24469step1Labels = mixedMoment B raw24469step2 raw24469step2Labels := by
      have ha : raw24469step2 = raw24469step1 := by apply Matrix.ext; unfold raw24469step2 raw24469step1; decide +kernel
      have hl : raw24469step1Labels = labelEmbedding6 ∘ raw24469step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24469step1 raw24469step1Labels raw24469step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4173 node4173Labels := by rfl

def raw24470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24470step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24470 raw24470Labels = mixedMoment B node4542 node4542Labels := by
  calc
    mixedMoment B raw24470 raw24470Labels = mixedMoment B raw24470step0 raw24470step0Labels := by
      have ha : raw24470step0 = (fun i j => raw24470 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24470step0 raw24470; decide +kernel
      have hl : raw24470step0Labels = raw24470Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24470 raw24470Labels permutation160 permutation3
    mixedMoment B raw24470step0 raw24470step0Labels = mixedMoment B raw24470step1 raw24470step1Labels := by
      have ha : raw24470step1 = raw24470step0 := by apply Matrix.ext; unfold raw24470step1 raw24470step0; decide +kernel
      have hl : raw24470step0Labels = labelEmbedding6 ∘ raw24470step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24470step0 raw24470step0Labels raw24470step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4542 node4542Labels := by rfl

def raw24471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24471step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24471step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24471 raw24471Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw24471 raw24471Labels = mixedMoment B raw24471step0 raw24471step0Labels := by
      have hz : ∀ j, raw24471 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24471step0 = (fun i j => raw24471 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24471step0 raw24471; decide +kernel
      have hl : raw24471step0Labels = raw24471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24471 raw24471Labels permutation265 hz
    mixedMoment B raw24471step0 raw24471step0Labels = mixedMoment B raw24471step1 raw24471step1Labels := by
      have ha : raw24471step1 = (fun i j => raw24471step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24471step1 raw24471step0; decide +kernel
      have hl : raw24471step1Labels = raw24471step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24471step0 raw24471step0Labels permutation40 permutation3
    mixedMoment B raw24471step1 raw24471step1Labels = mixedMoment B raw24471step2 raw24471step2Labels := by
      have ha : raw24471step2 = raw24471step1 := by apply Matrix.ext; unfold raw24471step2 raw24471step1; decide +kernel
      have hl : raw24471step1Labels = labelEmbedding6 ∘ raw24471step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24471step1 raw24471step1Labels raw24471step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw24472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24472step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24472step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24472 raw24472Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw24472 raw24472Labels = mixedMoment B raw24472step0 raw24472step0Labels := by
      have hz : ∀ j, raw24472 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24472step0 = (fun i j => raw24472 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24472step0 raw24472; decide +kernel
      have hl : raw24472step0Labels = raw24472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24472 raw24472Labels permutation265 hz
    mixedMoment B raw24472step0 raw24472step0Labels = mixedMoment B raw24472step1 raw24472step1Labels := by
      have ha : raw24472step1 = (fun i j => raw24472step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24472step1 raw24472step0; decide +kernel
      have hl : raw24472step1Labels = raw24472step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24472step0 raw24472step0Labels permutation46 permutation3
    mixedMoment B raw24472step1 raw24472step1Labels = mixedMoment B raw24472step2 raw24472step2Labels := by
      have ha : raw24472step2 = raw24472step1 := by apply Matrix.ext; unfold raw24472step2 raw24472step1; decide +kernel
      have hl : raw24472step1Labels = labelEmbedding6 ∘ raw24472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24472step1 raw24472step1Labels raw24472step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw24473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24473step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24473 raw24473Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw24473 raw24473Labels = mixedMoment B raw24473step0 raw24473step0Labels := by
      have hz : ∀ j, raw24473 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24473step0 = (fun i j => raw24473 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24473step0 raw24473; decide +kernel
      have hl : raw24473step0Labels = raw24473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24473 raw24473Labels permutation265 hz
    mixedMoment B raw24473step0 raw24473step0Labels = mixedMoment B raw24473step1 raw24473step1Labels := by
      have ha : raw24473step1 = (fun i j => raw24473step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24473step1 raw24473step0; decide +kernel
      have hl : raw24473step1Labels = raw24473step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24473step0 raw24473step0Labels permutation34 permutation3
    mixedMoment B raw24473step1 raw24473step1Labels = mixedMoment B raw24473step2 raw24473step2Labels := by
      have ha : raw24473step2 = raw24473step1 := by apply Matrix.ext; unfold raw24473step2 raw24473step1; decide +kernel
      have hl : raw24473step1Labels = labelEmbedding6 ∘ raw24473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24473step1 raw24473step1Labels raw24473step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4155 node4155Labels := by rfl

def raw24474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24474step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24474 raw24474Labels = mixedMoment B node4530 node4530Labels := by
  calc
    mixedMoment B raw24474 raw24474Labels = mixedMoment B raw24474step0 raw24474step0Labels := by
      have ha : raw24474step0 = (fun i j => raw24474 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24474step0 raw24474; decide +kernel
      have hl : raw24474step0Labels = raw24474Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24474 raw24474Labels permutation154 permutation3
    mixedMoment B raw24474step0 raw24474step0Labels = mixedMoment B raw24474step1 raw24474step1Labels := by
      have ha : raw24474step1 = raw24474step0 := by apply Matrix.ext; unfold raw24474step1 raw24474step0; decide +kernel
      have hl : raw24474step0Labels = labelEmbedding6 ∘ raw24474step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24474step0 raw24474step0Labels raw24474step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4530 node4530Labels := by rfl

def raw24475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24475 raw24475Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw24475 raw24475Labels = mixedMoment B raw24475step0 raw24475step0Labels := by
      have hz : ∀ j, raw24475 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24475step0 = (fun i j => raw24475 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24475step0 raw24475; decide +kernel
      have hl : raw24475step0Labels = raw24475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24475 raw24475Labels permutation265 hz
    mixedMoment B raw24475step0 raw24475step0Labels = mixedMoment B raw24475step1 raw24475step1Labels := by
      have ha : raw24475step1 = (fun i j => raw24475step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24475step1 raw24475step0; decide +kernel
      have hl : raw24475step1Labels = raw24475step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24475step0 raw24475step0Labels permutation34 permutation2
    _ = mixedMoment B node4554 node4554Labels := by rfl

def raw24476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24476 raw24476Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw24476 raw24476Labels = mixedMoment B raw24476step0 raw24476step0Labels := by
      have hz : ∀ j, raw24476 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24476step0 = (fun i j => raw24476 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24476step0 raw24476; decide +kernel
      have hl : raw24476step0Labels = raw24476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24476 raw24476Labels permutation265 hz
    mixedMoment B raw24476step0 raw24476step0Labels = mixedMoment B raw24476step1 raw24476step1Labels := by
      have ha : raw24476step1 = (fun i j => raw24476step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24476step1 raw24476step0; decide +kernel
      have hl : raw24476step1Labels = raw24476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24476step0 raw24476step0Labels permutation34 permutation2
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw24477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24477step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24477step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24477 raw24477Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw24477 raw24477Labels = mixedMoment B raw24477step0 raw24477step0Labels := by
      have hz : ∀ j, raw24477 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24477step0 = (fun i j => raw24477 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24477step0 raw24477; decide +kernel
      have hl : raw24477step0Labels = raw24477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24477 raw24477Labels permutation265 hz
    mixedMoment B raw24477step0 raw24477step0Labels = mixedMoment B raw24477step1 raw24477step1Labels := by
      have ha : raw24477step1 = (fun i j => raw24477step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24477step1 raw24477step0; decide +kernel
      have hl : raw24477step1Labels = raw24477step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24477step0 raw24477step0Labels permutation32 permutation3
    mixedMoment B raw24477step1 raw24477step1Labels = mixedMoment B raw24477step2 raw24477step2Labels := by
      have ha : raw24477step2 = raw24477step1 := by apply Matrix.ext; unfold raw24477step2 raw24477step1; decide +kernel
      have hl : raw24477step1Labels = labelEmbedding6 ∘ raw24477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24477step1 raw24477step1Labels raw24477step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4155 node4155Labels := by rfl

def raw24478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24478step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24478 raw24478Labels = mixedMoment B node4530 node4530Labels := by
  calc
    mixedMoment B raw24478 raw24478Labels = mixedMoment B raw24478step0 raw24478step0Labels := by
      have ha : raw24478step0 = (fun i j => raw24478 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24478step0 raw24478; decide +kernel
      have hl : raw24478step0Labels = raw24478Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24478 raw24478Labels permutation152 permutation3
    mixedMoment B raw24478step0 raw24478step0Labels = mixedMoment B raw24478step1 raw24478step1Labels := by
      have ha : raw24478step1 = raw24478step0 := by apply Matrix.ext; unfold raw24478step1 raw24478step0; decide +kernel
      have hl : raw24478step0Labels = labelEmbedding6 ∘ raw24478step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24478step0 raw24478step0Labels raw24478step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4530 node4530Labels := by rfl

def raw24479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24479 raw24479Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw24479 raw24479Labels = mixedMoment B raw24479step0 raw24479step0Labels := by
      have hz : ∀ j, raw24479 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24479step0 = (fun i j => raw24479 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24479step0 raw24479; decide +kernel
      have hl : raw24479step0Labels = raw24479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24479 raw24479Labels permutation265 hz
    _ = mixedMoment B node4554 node4554Labels := by rfl

def raw24480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24480 raw24480Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw24480 raw24480Labels = mixedMoment B raw24480step0 raw24480step0Labels := by
      have hz : ∀ j, raw24480 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24480step0 = (fun i j => raw24480 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24480step0 raw24480; decide +kernel
      have hl : raw24480step0Labels = raw24480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24480 raw24480Labels permutation265 hz
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw24481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24481step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24481step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24481 raw24481Labels = mixedMoment B node4151 node4151Labels := by
  calc
    mixedMoment B raw24481 raw24481Labels = mixedMoment B raw24481step0 raw24481step0Labels := by
      have hz : ∀ j, raw24481 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24481step0 = (fun i j => raw24481 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24481step0 raw24481; decide +kernel
      have hl : raw24481step0Labels = raw24481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24481 raw24481Labels permutation265 hz
    mixedMoment B raw24481step0 raw24481step0Labels = mixedMoment B raw24481step1 raw24481step1Labels := by
      have ha : raw24481step1 = (fun i j => raw24481step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24481step1 raw24481step0; decide +kernel
      have hl : raw24481step1Labels = raw24481step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24481step0 raw24481step0Labels permutation32 permutation3
    mixedMoment B raw24481step1 raw24481step1Labels = mixedMoment B raw24481step2 raw24481step2Labels := by
      have ha : raw24481step2 = raw24481step1 := by apply Matrix.ext; unfold raw24481step2 raw24481step1; decide +kernel
      have hl : raw24481step1Labels = labelEmbedding6 ∘ raw24481step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24481step1 raw24481step1Labels raw24481step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4151 node4151Labels := by rfl

def raw24482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24482step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24482 raw24482Labels = mixedMoment B node4527 node4527Labels := by
  calc
    mixedMoment B raw24482 raw24482Labels = mixedMoment B raw24482step0 raw24482step0Labels := by
      have ha : raw24482step0 = (fun i j => raw24482 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24482step0 raw24482; decide +kernel
      have hl : raw24482step0Labels = raw24482Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24482 raw24482Labels permutation152 permutation3
    mixedMoment B raw24482step0 raw24482step0Labels = mixedMoment B raw24482step1 raw24482step1Labels := by
      have ha : raw24482step1 = raw24482step0 := by apply Matrix.ext; unfold raw24482step1 raw24482step0; decide +kernel
      have hl : raw24482step0Labels = labelEmbedding6 ∘ raw24482step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24482step0 raw24482step0Labels raw24482step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4527 node4527Labels := by rfl

def raw24483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24483 raw24483Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw24483 raw24483Labels = mixedMoment B raw24483step0 raw24483step0Labels := by
      have hz : ∀ j, raw24483 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24483step0 = (fun i j => raw24483 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24483step0 raw24483; decide +kernel
      have hl : raw24483step0Labels = raw24483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24483 raw24483Labels permutation265 hz
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw24484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24484step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24484 raw24484Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw24484 raw24484Labels = mixedMoment B raw24484step0 raw24484step0Labels := by
      have hz : ∀ j, raw24484 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24484step0 = (fun i j => raw24484 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24484step0 raw24484; decide +kernel
      have hl : raw24484step0Labels = raw24484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24484 raw24484Labels permutation265 hz
    mixedMoment B raw24484step0 raw24484step0Labels = mixedMoment B raw24484step1 raw24484step1Labels := by
      have ha : raw24484step1 = (fun i j => raw24484step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24484step1 raw24484step0; decide +kernel
      have hl : raw24484step1Labels = raw24484step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24484step0 raw24484step0Labels permutation38 permutation3
    mixedMoment B raw24484step1 raw24484step1Labels = mixedMoment B raw24484step2 raw24484step2Labels := by
      have ha : raw24484step2 = raw24484step1 := by apply Matrix.ext; unfold raw24484step2 raw24484step1; decide +kernel
      have hl : raw24484step1Labels = labelEmbedding6 ∘ raw24484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24484step1 raw24484step1Labels raw24484step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw24485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24485 raw24485Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw24485 raw24485Labels = mixedMoment B raw24485step0 raw24485step0Labels := by
      have hz : ∀ j, raw24485 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24485step0 = (fun i j => raw24485 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24485step0 raw24485; decide +kernel
      have hl : raw24485step0Labels = raw24485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24485 raw24485Labels permutation265 hz
    mixedMoment B raw24485step0 raw24485step0Labels = mixedMoment B raw24485step1 raw24485step1Labels := by
      have ha : raw24485step1 = (fun i j => raw24485step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24485step1 raw24485step0; decide +kernel
      have hl : raw24485step1Labels = raw24485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24485step0 raw24485step0Labels permutation44 permutation3
    mixedMoment B raw24485step1 raw24485step1Labels = mixedMoment B raw24485step2 raw24485step2Labels := by
      have ha : raw24485step2 = raw24485step1 := by apply Matrix.ext; unfold raw24485step2 raw24485step1; decide +kernel
      have hl : raw24485step1Labels = labelEmbedding6 ∘ raw24485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24485step1 raw24485step1Labels raw24485step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw24486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24486 raw24486Labels = mixedMoment B node2936 node2936Labels := by
  calc
    mixedMoment B raw24486 raw24486Labels = mixedMoment B raw24486step0 raw24486step0Labels := by
      have ha : raw24486step0 = (fun i j => raw24486 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24486step0 raw24486; decide +kernel
      have hl : raw24486step0Labels = raw24486Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24486 raw24486Labels permutation152 permutation3
    _ = mixedMoment B node2936 node2936Labels := by rfl

def raw24487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24487 raw24487Labels = mixedMoment B node3000 node3000Labels := by
  calc
    mixedMoment B raw24487 raw24487Labels = mixedMoment B raw24487step0 raw24487step0Labels := by
      have hz : ∀ j, raw24487 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24487step0 = (fun i j => raw24487 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24487step0 raw24487; decide +kernel
      have hl : raw24487step0Labels = raw24487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24487 raw24487Labels permutation265 hz
    mixedMoment B raw24487step0 raw24487step0Labels = mixedMoment B raw24487step1 raw24487step1Labels := by
      have ha : raw24487step1 = (fun i j => raw24487step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24487step1 raw24487step0; decide +kernel
      have hl : raw24487step1Labels = raw24487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24487step0 raw24487step0Labels permutation32 permutation3
    _ = mixedMoment B node3000 node3000Labels := by rfl

def raw24488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24488 raw24488Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw24488 raw24488Labels = mixedMoment B raw24488step0 raw24488step0Labels := by
      have hz : ∀ j, raw24488 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24488step0 = (fun i j => raw24488 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24488step0 raw24488; decide +kernel
      have hl : raw24488step0Labels = raw24488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24488 raw24488Labels permutation265 hz
    mixedMoment B raw24488step0 raw24488step0Labels = mixedMoment B raw24488step1 raw24488step1Labels := by
      have ha : raw24488step1 = (fun i j => raw24488step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24488step1 raw24488step0; decide +kernel
      have hl : raw24488step1Labels = raw24488step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24488step0 raw24488step0Labels permutation38 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw24489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24489 raw24489Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw24489 raw24489Labels = mixedMoment B raw24489step0 raw24489step0Labels := by
      have hz : ∀ j, raw24489 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24489step0 = (fun i j => raw24489 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24489step0 raw24489; decide +kernel
      have hl : raw24489step0Labels = raw24489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24489 raw24489Labels permutation265 hz
    mixedMoment B raw24489step0 raw24489step0Labels = mixedMoment B raw24489step1 raw24489step1Labels := by
      have ha : raw24489step1 = (fun i j => raw24489step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24489step1 raw24489step0; decide +kernel
      have hl : raw24489step1Labels = raw24489step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24489step0 raw24489step0Labels permutation44 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw24490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw24490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24490 raw24490Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw24490 raw24490Labels = mixedMoment B raw24490step0 raw24490step0Labels := by
      have hz : ∀ j, raw24490 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24490step0 = (fun i j => raw24490 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24490step0 raw24490; decide +kernel
      have hl : raw24490step0Labels = raw24490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24490 raw24490Labels permutation265 hz
    mixedMoment B raw24490step0 raw24490step0Labels = mixedMoment B raw24490step1 raw24490step1Labels := by
      have ha : raw24490step1 = (fun i j => raw24490step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24490step1 raw24490step0; decide +kernel
      have hl : raw24490step1Labels = raw24490step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24490step0 raw24490step0Labels permutation32 permutation3
    _ = mixedMoment B node3111 node3111Labels := by rfl

def raw24491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24491 raw24491Labels = mixedMoment B node578 node578Labels := by
  calc
    mixedMoment B raw24491 raw24491Labels = mixedMoment B raw24491step0 raw24491step0Labels := by
      have ha : raw24491step0 = (fun i j => raw24491 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24491step0 raw24491; decide +kernel
      have hl : raw24491step0Labels = raw24491Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24491 raw24491Labels permutation184 permutation3
    _ = mixedMoment B node578 node578Labels := by rfl

def raw24492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24492 raw24492Labels = mixedMoment B node1162 node1162Labels := by
  calc
    mixedMoment B raw24492 raw24492Labels = mixedMoment B raw24492step0 raw24492step0Labels := by
      have ha : raw24492step0 = (fun i j => raw24492 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24492step0 raw24492; decide +kernel
      have hl : raw24492step0Labels = raw24492Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24492 raw24492Labels permutation184 permutation3
    _ = mixedMoment B node1162 node1162Labels := by rfl

def raw24493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24493 raw24493Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw24493 raw24493Labels = mixedMoment B raw24493step0 raw24493step0Labels := by
      have ha : raw24493step0 = (fun i j => raw24493 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24493step0 raw24493; decide +kernel
      have hl : raw24493step0Labels = raw24493Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24493 raw24493Labels permutation208 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw24494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24494 raw24494Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw24494 raw24494Labels = mixedMoment B raw24494step0 raw24494step0Labels := by
      have ha : raw24494step0 = (fun i j => raw24494 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24494step0 raw24494; decide +kernel
      have hl : raw24494step0Labels = raw24494Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24494 raw24494Labels permutation232 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw24495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24495 raw24495Labels = mixedMoment B node1265 node1265Labels := by
  calc
    mixedMoment B raw24495 raw24495Labels = mixedMoment B raw24495step0 raw24495step0Labels := by
      have ha : raw24495step0 = (fun i j => raw24495 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24495step0 raw24495; decide +kernel
      have hl : raw24495step0Labels = raw24495Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24495 raw24495Labels permutation185 permutation3
    _ = mixedMoment B node1265 node1265Labels := by rfl

def raw24496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24496 raw24496Labels = mixedMoment B node601 node601Labels := by
  calc
    mixedMoment B raw24496 raw24496Labels = mixedMoment B raw24496step0 raw24496step0Labels := by
      have hz : ∀ j, raw24496 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24496step0 = (fun i j => raw24496 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24496step0 raw24496; decide +kernel
      have hl : raw24496step0Labels = raw24496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24496 raw24496Labels permutation265 hz
    mixedMoment B raw24496step0 raw24496step0Labels = mixedMoment B raw24496step1 raw24496step1Labels := by
      have ha : raw24496step1 = (fun i j => raw24496step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24496step1 raw24496step0; decide +kernel
      have hl : raw24496step1Labels = raw24496step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24496step0 raw24496step0Labels permutation40 permutation3
    _ = mixedMoment B node601 node601Labels := by rfl

def raw24497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24497 raw24497Labels = mixedMoment B node1127 node1127Labels := by
  calc
    mixedMoment B raw24497 raw24497Labels = mixedMoment B raw24497step0 raw24497step0Labels := by
      have ha : raw24497step0 = (fun i j => raw24497 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24497step0 raw24497; decide +kernel
      have hl : raw24497step0Labels = raw24497Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24497 raw24497Labels permutation160 permutation3
    _ = mixedMoment B node1127 node1127Labels := by rfl

def raw24498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24498 raw24498Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw24498 raw24498Labels = mixedMoment B raw24498step0 raw24498step0Labels := by
      have hz : ∀ j, raw24498 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24498step0 = (fun i j => raw24498 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24498step0 raw24498; decide +kernel
      have hl : raw24498step0Labels = raw24498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24498 raw24498Labels permutation265 hz
    mixedMoment B raw24498step0 raw24498step0Labels = mixedMoment B raw24498step1 raw24498step1Labels := by
      have ha : raw24498step1 = (fun i j => raw24498step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24498step1 raw24498step0; decide +kernel
      have hl : raw24498step1Labels = raw24498step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24498step0 raw24498step0Labels permutation40 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw24499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24499 raw24499Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw24499 raw24499Labels = mixedMoment B raw24499step0 raw24499step0Labels := by
      have hz : ∀ j, raw24499 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24499step0 = (fun i j => raw24499 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24499step0 raw24499; decide +kernel
      have hl : raw24499step0Labels = raw24499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24499 raw24499Labels permutation265 hz
    mixedMoment B raw24499step0 raw24499step0Labels = mixedMoment B raw24499step1 raw24499step1Labels := by
      have ha : raw24499step1 = (fun i j => raw24499step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24499step1 raw24499step0; decide +kernel
      have hl : raw24499step1Labels = raw24499step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24499step0 raw24499step0Labels permutation46 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw24500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24500 raw24500Labels = mixedMoment B node1298 node1298Labels := by
  calc
    mixedMoment B raw24500 raw24500Labels = mixedMoment B raw24500step0 raw24500step0Labels := by
      have hz : ∀ j, raw24500 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24500step0 = (fun i j => raw24500 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24500step0 raw24500; decide +kernel
      have hl : raw24500step0Labels = raw24500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24500 raw24500Labels permutation265 hz
    mixedMoment B raw24500step0 raw24500step0Labels = mixedMoment B raw24500step1 raw24500step1Labels := by
      have ha : raw24500step1 = (fun i j => raw24500step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24500step1 raw24500step0; decide +kernel
      have hl : raw24500step1Labels = raw24500step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24500step0 raw24500step0Labels permutation41 permutation3
    _ = mixedMoment B node1298 node1298Labels := by rfl

def raw24501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24501 raw24501Labels = mixedMoment B node583 node583Labels := by
  calc
    mixedMoment B raw24501 raw24501Labels = mixedMoment B raw24501step0 raw24501step0Labels := by
      have hz : ∀ j, raw24501 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24501step0 = (fun i j => raw24501 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24501step0 raw24501; decide +kernel
      have hl : raw24501step0Labels = raw24501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24501 raw24501Labels permutation265 hz
    mixedMoment B raw24501step0 raw24501step0Labels = mixedMoment B raw24501step1 raw24501step1Labels := by
      have ha : raw24501step1 = (fun i j => raw24501step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24501step1 raw24501step0; decide +kernel
      have hl : raw24501step1Labels = raw24501step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24501step0 raw24501step0Labels permutation34 permutation3
    _ = mixedMoment B node583 node583Labels := by rfl

def raw24502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24502 raw24502Labels = mixedMoment B node1114 node1114Labels := by
  calc
    mixedMoment B raw24502 raw24502Labels = mixedMoment B raw24502step0 raw24502step0Labels := by
      have ha : raw24502step0 = (fun i j => raw24502 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24502step0 raw24502; decide +kernel
      have hl : raw24502step0Labels = raw24502Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24502 raw24502Labels permutation154 permutation3
    _ = mixedMoment B node1114 node1114Labels := by rfl

def raw24503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24503 raw24503Labels = mixedMoment B node1167 node1167Labels := by
  calc
    mixedMoment B raw24503 raw24503Labels = mixedMoment B raw24503step0 raw24503step0Labels := by
      have hz : ∀ j, raw24503 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24503step0 = (fun i j => raw24503 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24503step0 raw24503; decide +kernel
      have hl : raw24503step0Labels = raw24503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24503 raw24503Labels permutation265 hz
    mixedMoment B raw24503step0 raw24503step0Labels = mixedMoment B raw24503step1 raw24503step1Labels := by
      have ha : raw24503step1 = (fun i j => raw24503step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24503step1 raw24503step0; decide +kernel
      have hl : raw24503step1Labels = raw24503step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24503step0 raw24503step0Labels permutation34 permutation3
    _ = mixedMoment B node1167 node1167Labels := by rfl

def raw24504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24504 raw24504Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw24504 raw24504Labels = mixedMoment B raw24504step0 raw24504step0Labels := by
      have hz : ∀ j, raw24504 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24504step0 = (fun i j => raw24504 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24504step0 raw24504; decide +kernel
      have hl : raw24504step0Labels = raw24504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24504 raw24504Labels permutation265 hz
    mixedMoment B raw24504step0 raw24504step0Labels = mixedMoment B raw24504step1 raw24504step1Labels := by
      have ha : raw24504step1 = (fun i j => raw24504step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24504step1 raw24504step0; decide +kernel
      have hl : raw24504step1Labels = raw24504step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24504step0 raw24504step0Labels permutation44 permutation3
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw24505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24505 raw24505Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw24505 raw24505Labels = mixedMoment B raw24505step0 raw24505step0Labels := by
      have hz : ∀ j, raw24505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24505step0 = (fun i j => raw24505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24505step0 raw24505; decide +kernel
      have hl : raw24505step0Labels = raw24505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24505 raw24505Labels permutation265 hz
    mixedMoment B raw24505step0 raw24505step0Labels = mixedMoment B raw24505step1 raw24505step1Labels := by
      have ha : raw24505step1 = (fun i j => raw24505step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24505step1 raw24505step0; decide +kernel
      have hl : raw24505step1Labels = raw24505step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24505step0 raw24505step0Labels permutation35 permutation3
    _ = mixedMoment B node1266 node1266Labels := by rfl

def raw24506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24506 raw24506Labels = mixedMoment B node583 node583Labels := by
  calc
    mixedMoment B raw24506 raw24506Labels = mixedMoment B raw24506step0 raw24506step0Labels := by
      have hz : ∀ j, raw24506 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24506step0 = (fun i j => raw24506 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24506step0 raw24506; decide +kernel
      have hl : raw24506step0Labels = raw24506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24506 raw24506Labels permutation265 hz
    mixedMoment B raw24506step0 raw24506step0Labels = mixedMoment B raw24506step1 raw24506step1Labels := by
      have ha : raw24506step1 = (fun i j => raw24506step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24506step1 raw24506step0; decide +kernel
      have hl : raw24506step1Labels = raw24506step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24506step0 raw24506step0Labels permutation32 permutation3
    _ = mixedMoment B node583 node583Labels := by rfl

def raw24507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24507 raw24507Labels = mixedMoment B node1114 node1114Labels := by
  calc
    mixedMoment B raw24507 raw24507Labels = mixedMoment B raw24507step0 raw24507step0Labels := by
      have ha : raw24507step0 = (fun i j => raw24507 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24507step0 raw24507; decide +kernel
      have hl : raw24507step0Labels = raw24507Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24507 raw24507Labels permutation152 permutation3
    _ = mixedMoment B node1114 node1114Labels := by rfl

def raw24508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24508 raw24508Labels = mixedMoment B node1167 node1167Labels := by
  calc
    mixedMoment B raw24508 raw24508Labels = mixedMoment B raw24508step0 raw24508step0Labels := by
      have hz : ∀ j, raw24508 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24508step0 = (fun i j => raw24508 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24508step0 raw24508; decide +kernel
      have hl : raw24508step0Labels = raw24508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24508 raw24508Labels permutation265 hz
    mixedMoment B raw24508step0 raw24508step0Labels = mixedMoment B raw24508step1 raw24508step1Labels := by
      have ha : raw24508step1 = (fun i j => raw24508step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24508step1 raw24508step0; decide +kernel
      have hl : raw24508step1Labels = raw24508step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24508step0 raw24508step0Labels permutation32 permutation3
    _ = mixedMoment B node1167 node1167Labels := by rfl

def raw24509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24509 raw24509Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw24509 raw24509Labels = mixedMoment B raw24509step0 raw24509step0Labels := by
      have hz : ∀ j, raw24509 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24509step0 = (fun i j => raw24509 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24509step0 raw24509; decide +kernel
      have hl : raw24509step0Labels = raw24509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24509 raw24509Labels permutation265 hz
    mixedMoment B raw24509step0 raw24509step0Labels = mixedMoment B raw24509step1 raw24509step1Labels := by
      have ha : raw24509step1 = (fun i j => raw24509step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24509step1 raw24509step0; decide +kernel
      have hl : raw24509step1Labels = raw24509step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24509step0 raw24509step0Labels permutation38 permutation3
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw24510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw24510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw24510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24510 raw24510Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw24510 raw24510Labels = mixedMoment B raw24510step0 raw24510step0Labels := by
      have hz : ∀ j, raw24510 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24510step0 = (fun i j => raw24510 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24510step0 raw24510; decide +kernel
      have hl : raw24510step0Labels = raw24510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24510 raw24510Labels permutation265 hz
    mixedMoment B raw24510step0 raw24510step0Labels = mixedMoment B raw24510step1 raw24510step1Labels := by
      have ha : raw24510step1 = (fun i j => raw24510step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24510step1 raw24510step0; decide +kernel
      have hl : raw24510step1Labels = raw24510step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24510step0 raw24510step0Labels permutation33 permutation3
    _ = mixedMoment B node1266 node1266Labels := by rfl

def raw24511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24511 raw24511Labels = mixedMoment B node579 node579Labels := by
  calc
    mixedMoment B raw24511 raw24511Labels = mixedMoment B raw24511step0 raw24511step0Labels := by
      have hz : ∀ j, raw24511 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24511step0 = (fun i j => raw24511 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24511step0 raw24511; decide +kernel
      have hl : raw24511step0Labels = raw24511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24511 raw24511Labels permutation265 hz
    mixedMoment B raw24511step0 raw24511step0Labels = mixedMoment B raw24511step1 raw24511step1Labels := by
      have ha : raw24511step1 = (fun i j => raw24511step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24511step1 raw24511step0; decide +kernel
      have hl : raw24511step1Labels = raw24511step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24511step0 raw24511step0Labels permutation32 permutation3
    _ = mixedMoment B node579 node579Labels := by rfl

def raw24512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24512 raw24512Labels = mixedMoment B node1111 node1111Labels := by
  calc
    mixedMoment B raw24512 raw24512Labels = mixedMoment B raw24512step0 raw24512step0Labels := by
      have ha : raw24512step0 = (fun i j => raw24512 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24512step0 raw24512; decide +kernel
      have hl : raw24512step0Labels = raw24512Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24512 raw24512Labels permutation152 permutation3
    _ = mixedMoment B node1111 node1111Labels := by rfl

def raw24513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24513 raw24513Labels = mixedMoment B node1163 node1163Labels := by
  calc
    mixedMoment B raw24513 raw24513Labels = mixedMoment B raw24513step0 raw24513step0Labels := by
      have hz : ∀ j, raw24513 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24513step0 = (fun i j => raw24513 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24513step0 raw24513; decide +kernel
      have hl : raw24513step0Labels = raw24513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24513 raw24513Labels permutation265 hz
    mixedMoment B raw24513step0 raw24513step0Labels = mixedMoment B raw24513step1 raw24513step1Labels := by
      have ha : raw24513step1 = (fun i j => raw24513step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24513step1 raw24513step0; decide +kernel
      have hl : raw24513step1Labels = raw24513step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24513step0 raw24513step0Labels permutation32 permutation3
    _ = mixedMoment B node1163 node1163Labels := by rfl

def raw24514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24514 raw24514Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw24514 raw24514Labels = mixedMoment B raw24514step0 raw24514step0Labels := by
      have hz : ∀ j, raw24514 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24514step0 = (fun i j => raw24514 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24514step0 raw24514; decide +kernel
      have hl : raw24514step0Labels = raw24514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24514 raw24514Labels permutation265 hz
    mixedMoment B raw24514step0 raw24514step0Labels = mixedMoment B raw24514step1 raw24514step1Labels := by
      have ha : raw24514step1 = (fun i j => raw24514step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24514step1 raw24514step0; decide +kernel
      have hl : raw24514step1Labels = raw24514step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24514step0 raw24514step0Labels permutation38 permutation3
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw24515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24515 raw24515Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw24515 raw24515Labels = mixedMoment B raw24515step0 raw24515step0Labels := by
      have hz : ∀ j, raw24515 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24515step0 = (fun i j => raw24515 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24515step0 raw24515; decide +kernel
      have hl : raw24515step0Labels = raw24515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24515 raw24515Labels permutation265 hz
    mixedMoment B raw24515step0 raw24515step0Labels = mixedMoment B raw24515step1 raw24515step1Labels := by
      have ha : raw24515step1 = (fun i j => raw24515step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24515step1 raw24515step0; decide +kernel
      have hl : raw24515step1Labels = raw24515step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24515step0 raw24515step0Labels permutation44 permutation3
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw24516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24516 raw24516Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw24516 raw24516Labels = mixedMoment B raw24516step0 raw24516step0Labels := by
      have ha : raw24516step0 = (fun i j => raw24516 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24516step0 raw24516; decide +kernel
      have hl : raw24516step0Labels = raw24516Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24516 raw24516Labels permutation176 permutation7
    mixedMoment B raw24516step0 raw24516step0Labels = mixedMoment B raw24516step1 raw24516step1Labels := by
      have ha : raw24516step1 = -raw24516step0 := by apply Matrix.ext; change ∀ i j, raw24516step1 i j = -(raw24516step0 i j); unfold raw24516step1 raw24516step0; decide +kernel
      have hl : raw24516step1Labels = raw24516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24516step1 raw24516step1Labels = mixedMoment B raw24516step2 raw24516step2Labels := by
      have ha : raw24516step2 = raw24516step1 := by apply Matrix.ext; unfold raw24516step2 raw24516step1; decide +kernel
      have hl : raw24516step1Labels = labelEmbedding1 ∘ raw24516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24516step1 raw24516step1Labels raw24516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw24517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24517 raw24517Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw24517 raw24517Labels = mixedMoment B raw24517step0 raw24517step0Labels := by
      have hz : ∀ j, raw24517 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24517step0 = (fun i j => raw24517 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24517step0 raw24517; decide +kernel
      have hl : raw24517step0Labels = raw24517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24517 raw24517Labels permutation265 hz
    mixedMoment B raw24517step0 raw24517step0Labels = mixedMoment B raw24517step1 raw24517step1Labels := by
      have ha : raw24517step1 = (fun i j => raw24517step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24517step1 raw24517step0; decide +kernel
      have hl : raw24517step1Labels = raw24517step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24517step0 raw24517step0Labels permutation32 permutation7
    mixedMoment B raw24517step1 raw24517step1Labels = mixedMoment B raw24517step2 raw24517step2Labels := by
      have ha : raw24517step2 = -raw24517step1 := by apply Matrix.ext; change ∀ i j, raw24517step2 i j = -(raw24517step1 i j); unfold raw24517step2 raw24517step1; decide +kernel
      have hl : raw24517step2Labels = raw24517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24517step2 raw24517step2Labels = mixedMoment B raw24517step3 raw24517step3Labels := by
      have ha : raw24517step3 = raw24517step2 := by apply Matrix.ext; unfold raw24517step3 raw24517step2; decide +kernel
      have hl : raw24517step2Labels = labelEmbedding1 ∘ raw24517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24517step2 raw24517step2Labels raw24517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

def raw24518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24518step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24518 raw24518Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw24518 raw24518Labels = mixedMoment B raw24518step0 raw24518step0Labels := by
      have hz : ∀ j, raw24518 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24518step0 = (fun i j => raw24518 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24518step0 raw24518; decide +kernel
      have hl : raw24518step0Labels = raw24518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24518 raw24518Labels permutation265 hz
    mixedMoment B raw24518step0 raw24518step0Labels = mixedMoment B raw24518step1 raw24518step1Labels := by
      have ha : raw24518step1 = (fun i j => raw24518step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24518step1 raw24518step0; decide +kernel
      have hl : raw24518step1Labels = raw24518step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24518step0 raw24518step0Labels permutation32 permutation7
    mixedMoment B raw24518step1 raw24518step1Labels = mixedMoment B raw24518step2 raw24518step2Labels := by
      have ha : raw24518step2 = -raw24518step1 := by apply Matrix.ext; change ∀ i j, raw24518step2 i j = -(raw24518step1 i j); unfold raw24518step2 raw24518step1; decide +kernel
      have hl : raw24518step2Labels = raw24518step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24518step2 raw24518step2Labels = mixedMoment B raw24518step3 raw24518step3Labels := by
      have ha : raw24518step3 = raw24518step2 := by apply Matrix.ext; unfold raw24518step3 raw24518step2; decide +kernel
      have hl : raw24518step2Labels = labelEmbedding1 ∘ raw24518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24518step2 raw24518step2Labels raw24518step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw24519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24519step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24519step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24519step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24519 raw24519Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw24519 raw24519Labels = mixedMoment B raw24519step0 raw24519step0Labels := by
      have hz : ∀ j, raw24519 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24519step0 = (fun i j => raw24519 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24519step0 raw24519; decide +kernel
      have hl : raw24519step0Labels = raw24519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24519 raw24519Labels permutation265 hz
    mixedMoment B raw24519step0 raw24519step0Labels = mixedMoment B raw24519step1 raw24519step1Labels := by
      have ha : raw24519step1 = (fun i j => raw24519step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24519step1 raw24519step0; decide +kernel
      have hl : raw24519step1Labels = raw24519step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24519step0 raw24519step0Labels permutation34 permutation7
    mixedMoment B raw24519step1 raw24519step1Labels = mixedMoment B raw24519step2 raw24519step2Labels := by
      have ha : raw24519step2 = -raw24519step1 := by apply Matrix.ext; change ∀ i j, raw24519step2 i j = -(raw24519step1 i j); unfold raw24519step2 raw24519step1; decide +kernel
      have hl : raw24519step2Labels = raw24519step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24519step2 raw24519step2Labels = mixedMoment B raw24519step3 raw24519step3Labels := by
      have ha : raw24519step3 = raw24519step2 := by apply Matrix.ext; unfold raw24519step3 raw24519step2; decide +kernel
      have hl : raw24519step2Labels = labelEmbedding1 ∘ raw24519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24519step2 raw24519step2Labels raw24519step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw24520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw24520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24520step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24520step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24520 raw24520Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw24520 raw24520Labels = mixedMoment B raw24520step0 raw24520step0Labels := by
      have hz : ∀ j, raw24520 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24520step0 = (fun i j => raw24520 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24520step0 raw24520; decide +kernel
      have hl : raw24520step0Labels = raw24520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24520 raw24520Labels permutation265 hz
    mixedMoment B raw24520step0 raw24520step0Labels = mixedMoment B raw24520step1 raw24520step1Labels := by
      have ha : raw24520step1 = (fun i j => raw24520step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24520step1 raw24520step0; decide +kernel
      have hl : raw24520step1Labels = raw24520step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24520step0 raw24520step0Labels permutation32 permutation7
    mixedMoment B raw24520step1 raw24520step1Labels = mixedMoment B raw24520step2 raw24520step2Labels := by
      have ha : raw24520step2 = -raw24520step1 := by apply Matrix.ext; change ∀ i j, raw24520step2 i j = -(raw24520step1 i j); unfold raw24520step2 raw24520step1; decide +kernel
      have hl : raw24520step2Labels = raw24520step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24520step2 raw24520step2Labels = mixedMoment B raw24520step3 raw24520step3Labels := by
      have ha : raw24520step3 = raw24520step2 := by apply Matrix.ext; unfold raw24520step3 raw24520step2; decide +kernel
      have hl : raw24520step2Labels = labelEmbedding1 ∘ raw24520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24520step2 raw24520step2Labels raw24520step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

def raw24521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24521step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24521step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24521 raw24521Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw24521 raw24521Labels = mixedMoment B raw24521step0 raw24521step0Labels := by
      have ha : raw24521step0 = (fun i j => raw24521 (permutation214 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24521step0 raw24521; decide +kernel
      have hl : raw24521step0Labels = raw24521Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24521 raw24521Labels permutation214 permutation5
    mixedMoment B raw24521step0 raw24521step0Labels = mixedMoment B raw24521step1 raw24521step1Labels := by
      have ha : raw24521step1 = -raw24521step0 := by apply Matrix.ext; change ∀ i j, raw24521step1 i j = -(raw24521step0 i j); unfold raw24521step1 raw24521step0; decide +kernel
      have hl : raw24521step1Labels = raw24521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24521step1 raw24521step1Labels = mixedMoment B raw24521step2 raw24521step2Labels := by
      have ha : raw24521step2 = raw24521step1 := by apply Matrix.ext; unfold raw24521step2 raw24521step1; decide +kernel
      have hl : raw24521step1Labels = labelEmbedding1 ∘ raw24521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24521step1 raw24521step1Labels raw24521step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

def raw24522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24522 raw24522Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw24522 raw24522Labels = mixedMoment B raw24522step0 raw24522step0Labels := by
      have ha : raw24522step0 = (fun i j => raw24522 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24522step0 raw24522; decide +kernel
      have hl : raw24522step0Labels = raw24522Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24522 raw24522Labels permutation176 permutation7
    mixedMoment B raw24522step0 raw24522step0Labels = mixedMoment B raw24522step1 raw24522step1Labels := by
      have ha : raw24522step1 = -raw24522step0 := by apply Matrix.ext; change ∀ i j, raw24522step1 i j = -(raw24522step0 i j); unfold raw24522step1 raw24522step0; decide +kernel
      have hl : raw24522step1Labels = raw24522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24522step1 raw24522step1Labels = mixedMoment B raw24522step2 raw24522step2Labels := by
      have ha : raw24522step2 = raw24522step1 := by apply Matrix.ext; unfold raw24522step2 raw24522step1; decide +kernel
      have hl : raw24522step1Labels = labelEmbedding1 ∘ raw24522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24522step1 raw24522step1Labels raw24522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

def raw24523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24523step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24523 raw24523Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw24523 raw24523Labels = mixedMoment B raw24523step0 raw24523step0Labels := by
      have ha : raw24523step0 = (fun i j => raw24523 (permutation214 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24523step0 raw24523; decide +kernel
      have hl : raw24523step0Labels = raw24523Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24523 raw24523Labels permutation214 permutation5
    mixedMoment B raw24523step0 raw24523step0Labels = mixedMoment B raw24523step1 raw24523step1Labels := by
      have ha : raw24523step1 = -raw24523step0 := by apply Matrix.ext; change ∀ i j, raw24523step1 i j = -(raw24523step0 i j); unfold raw24523step1 raw24523step0; decide +kernel
      have hl : raw24523step1Labels = raw24523step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24523step1 raw24523step1Labels = mixedMoment B raw24523step2 raw24523step2Labels := by
      have ha : raw24523step2 = raw24523step1 := by apply Matrix.ext; unfold raw24523step2 raw24523step1; decide +kernel
      have hl : raw24523step1Labels = labelEmbedding1 ∘ raw24523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24523step1 raw24523step1Labels raw24523step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw24524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24524step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24524step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24524 raw24524Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw24524 raw24524Labels = mixedMoment B raw24524step0 raw24524step0Labels := by
      have ha : raw24524step0 = (fun i j => raw24524 (permutation236 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24524step0 raw24524; decide +kernel
      have hl : raw24524step0Labels = raw24524Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24524 raw24524Labels permutation236 permutation5
    mixedMoment B raw24524step0 raw24524step0Labels = mixedMoment B raw24524step1 raw24524step1Labels := by
      have ha : raw24524step1 = -raw24524step0 := by apply Matrix.ext; change ∀ i j, raw24524step1 i j = -(raw24524step0 i j); unfold raw24524step1 raw24524step0; decide +kernel
      have hl : raw24524step1Labels = raw24524step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24524step1 raw24524step1Labels = mixedMoment B raw24524step2 raw24524step2Labels := by
      have ha : raw24524step2 = raw24524step1 := by apply Matrix.ext; unfold raw24524step2 raw24524step1; decide +kernel
      have hl : raw24524step1Labels = labelEmbedding1 ∘ raw24524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24524step1 raw24524step1Labels raw24524step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw24525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw24525step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24525step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24525step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24525 raw24525Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw24525 raw24525Labels = mixedMoment B raw24525step0 raw24525step0Labels := by
      have ha : raw24525step0 = (fun i j => raw24525 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24525step0 raw24525; decide +kernel
      have hl : raw24525step0Labels = raw24525Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24525 raw24525Labels permutation176 permutation7
    mixedMoment B raw24525step0 raw24525step0Labels = mixedMoment B raw24525step1 raw24525step1Labels := by
      have ha : raw24525step1 = -raw24525step0 := by apply Matrix.ext; change ∀ i j, raw24525step1 i j = -(raw24525step0 i j); unfold raw24525step1 raw24525step0; decide +kernel
      have hl : raw24525step1Labels = raw24525step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24525step1 raw24525step1Labels = mixedMoment B raw24525step2 raw24525step2Labels := by
      have ha : raw24525step2 = raw24525step1 := by apply Matrix.ext; unfold raw24525step2 raw24525step1; decide +kernel
      have hl : raw24525step1Labels = labelEmbedding1 ∘ raw24525step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24525step1 raw24525step1Labels raw24525step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

def raw24526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24526step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24526step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24526 raw24526Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw24526 raw24526Labels = mixedMoment B raw24526step0 raw24526step0Labels := by
      have hz : ∀ j, raw24526 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24526step0 = (fun i j => raw24526 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24526step0 raw24526; decide +kernel
      have hl : raw24526step0Labels = raw24526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24526 raw24526Labels permutation265 hz
    mixedMoment B raw24526step0 raw24526step0Labels = mixedMoment B raw24526step1 raw24526step1Labels := by
      have ha : raw24526step1 = (fun i j => raw24526step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24526step1 raw24526step0; decide +kernel
      have hl : raw24526step1Labels = raw24526step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24526step0 raw24526step0Labels permutation41 permutation5
    mixedMoment B raw24526step1 raw24526step1Labels = mixedMoment B raw24526step2 raw24526step2Labels := by
      have ha : raw24526step2 = -raw24526step1 := by apply Matrix.ext; change ∀ i j, raw24526step2 i j = -(raw24526step1 i j); unfold raw24526step2 raw24526step1; decide +kernel
      have hl : raw24526step2Labels = raw24526step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24526step2 raw24526step2Labels = mixedMoment B raw24526step3 raw24526step3Labels := by
      have ha : raw24526step3 = raw24526step2 := by apply Matrix.ext; unfold raw24526step3 raw24526step2; decide +kernel
      have hl : raw24526step2Labels = labelEmbedding1 ∘ raw24526step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24526step2 raw24526step2Labels raw24526step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

def raw24527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24527step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24527step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24527 raw24527Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw24527 raw24527Labels = mixedMoment B raw24527step0 raw24527step0Labels := by
      have ha : raw24527step0 = (fun i j => raw24527 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24527step0 raw24527; decide +kernel
      have hl : raw24527step0Labels = raw24527Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24527 raw24527Labels permutation161 permutation5
    mixedMoment B raw24527step0 raw24527step0Labels = mixedMoment B raw24527step1 raw24527step1Labels := by
      have ha : raw24527step1 = -raw24527step0 := by apply Matrix.ext; change ∀ i j, raw24527step1 i j = -(raw24527step0 i j); unfold raw24527step1 raw24527step0; decide +kernel
      have hl : raw24527step1Labels = raw24527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24527step1 raw24527step1Labels = mixedMoment B raw24527step2 raw24527step2Labels := by
      have ha : raw24527step2 = raw24527step1 := by apply Matrix.ext; unfold raw24527step2 raw24527step1; decide +kernel
      have hl : raw24527step1Labels = labelEmbedding1 ∘ raw24527step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24527step1 raw24527step1Labels raw24527step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

def raw24528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24528step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24528step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24528step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24528 raw24528Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw24528 raw24528Labels = mixedMoment B raw24528step0 raw24528step0Labels := by
      have hz : ∀ j, raw24528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24528step0 = (fun i j => raw24528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24528step0 raw24528; decide +kernel
      have hl : raw24528step0Labels = raw24528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24528 raw24528Labels permutation265 hz
    mixedMoment B raw24528step0 raw24528step0Labels = mixedMoment B raw24528step1 raw24528step1Labels := by
      have ha : raw24528step1 = (fun i j => raw24528step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24528step1 raw24528step0; decide +kernel
      have hl : raw24528step1Labels = raw24528step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24528step0 raw24528step0Labels permutation41 permutation5
    mixedMoment B raw24528step1 raw24528step1Labels = mixedMoment B raw24528step2 raw24528step2Labels := by
      have ha : raw24528step2 = -raw24528step1 := by apply Matrix.ext; change ∀ i j, raw24528step2 i j = -(raw24528step1 i j); unfold raw24528step2 raw24528step1; decide +kernel
      have hl : raw24528step2Labels = raw24528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24528step2 raw24528step2Labels = mixedMoment B raw24528step3 raw24528step3Labels := by
      have ha : raw24528step3 = raw24528step2 := by apply Matrix.ext; unfold raw24528step3 raw24528step2; decide +kernel
      have hl : raw24528step2Labels = labelEmbedding1 ∘ raw24528step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24528step2 raw24528step2Labels raw24528step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw24529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24529step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24529step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24529step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24529step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24529 raw24529Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw24529 raw24529Labels = mixedMoment B raw24529step0 raw24529step0Labels := by
      have hz : ∀ j, raw24529 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24529step0 = (fun i j => raw24529 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24529step0 raw24529; decide +kernel
      have hl : raw24529step0Labels = raw24529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24529 raw24529Labels permutation265 hz
    mixedMoment B raw24529step0 raw24529step0Labels = mixedMoment B raw24529step1 raw24529step1Labels := by
      have ha : raw24529step1 = (fun i j => raw24529step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24529step1 raw24529step0; decide +kernel
      have hl : raw24529step1Labels = raw24529step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24529step0 raw24529step0Labels permutation47 permutation5
    mixedMoment B raw24529step1 raw24529step1Labels = mixedMoment B raw24529step2 raw24529step2Labels := by
      have ha : raw24529step2 = -raw24529step1 := by apply Matrix.ext; change ∀ i j, raw24529step2 i j = -(raw24529step1 i j); unfold raw24529step2 raw24529step1; decide +kernel
      have hl : raw24529step2Labels = raw24529step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24529step2 raw24529step2Labels = mixedMoment B raw24529step3 raw24529step3Labels := by
      have ha : raw24529step3 = raw24529step2 := by apply Matrix.ext; unfold raw24529step3 raw24529step2; decide +kernel
      have hl : raw24529step2Labels = labelEmbedding1 ∘ raw24529step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24529step2 raw24529step2Labels raw24529step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw24530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw24530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24530step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24530step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24530 raw24530Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw24530 raw24530Labels = mixedMoment B raw24530step0 raw24530step0Labels := by
      have hz : ∀ j, raw24530 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24530step0 = (fun i j => raw24530 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24530step0 raw24530; decide +kernel
      have hl : raw24530step0Labels = raw24530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24530 raw24530Labels permutation265 hz
    mixedMoment B raw24530step0 raw24530step0Labels = mixedMoment B raw24530step1 raw24530step1Labels := by
      have ha : raw24530step1 = (fun i j => raw24530step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24530step1 raw24530step0; decide +kernel
      have hl : raw24530step1Labels = raw24530step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24530step0 raw24530step0Labels permutation32 permutation7
    mixedMoment B raw24530step1 raw24530step1Labels = mixedMoment B raw24530step2 raw24530step2Labels := by
      have ha : raw24530step2 = -raw24530step1 := by apply Matrix.ext; change ∀ i j, raw24530step2 i j = -(raw24530step1 i j); unfold raw24530step2 raw24530step1; decide +kernel
      have hl : raw24530step2Labels = raw24530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24530step2 raw24530step2Labels = mixedMoment B raw24530step3 raw24530step3Labels := by
      have ha : raw24530step3 = raw24530step2 := by apply Matrix.ext; unfold raw24530step3 raw24530step2; decide +kernel
      have hl : raw24530step2Labels = labelEmbedding1 ∘ raw24530step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24530step2 raw24530step2Labels raw24530step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

def raw24531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24531step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24531step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24531step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24531step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24531 raw24531Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw24531 raw24531Labels = mixedMoment B raw24531step0 raw24531step0Labels := by
      have hz : ∀ j, raw24531 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24531step0 = (fun i j => raw24531 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24531step0 raw24531; decide +kernel
      have hl : raw24531step0Labels = raw24531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24531 raw24531Labels permutation265 hz
    mixedMoment B raw24531step0 raw24531step0Labels = mixedMoment B raw24531step1 raw24531step1Labels := by
      have ha : raw24531step1 = (fun i j => raw24531step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24531step1 raw24531step0; decide +kernel
      have hl : raw24531step1Labels = raw24531step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24531step0 raw24531step0Labels permutation44 permutation5
    mixedMoment B raw24531step1 raw24531step1Labels = mixedMoment B raw24531step2 raw24531step2Labels := by
      have ha : raw24531step2 = -raw24531step1 := by apply Matrix.ext; change ∀ i j, raw24531step2 i j = -(raw24531step1 i j); unfold raw24531step2 raw24531step1; decide +kernel
      have hl : raw24531step2Labels = raw24531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24531step2 raw24531step2Labels = mixedMoment B raw24531step3 raw24531step3Labels := by
      have ha : raw24531step3 = raw24531step2 := by apply Matrix.ext; unfold raw24531step3 raw24531step2; decide +kernel
      have hl : raw24531step2Labels = labelEmbedding1 ∘ raw24531step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24531step2 raw24531step2Labels raw24531step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

def raw24532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24532step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24532step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24532 raw24532Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw24532 raw24532Labels = mixedMoment B raw24532step0 raw24532step0Labels := by
      have ha : raw24532step0 = (fun i j => raw24532 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24532step0 raw24532; decide +kernel
      have hl : raw24532step0Labels = raw24532Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24532 raw24532Labels permutation164 permutation5
    mixedMoment B raw24532step0 raw24532step0Labels = mixedMoment B raw24532step1 raw24532step1Labels := by
      have ha : raw24532step1 = -raw24532step0 := by apply Matrix.ext; change ∀ i j, raw24532step1 i j = -(raw24532step0 i j); unfold raw24532step1 raw24532step0; decide +kernel
      have hl : raw24532step1Labels = raw24532step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24532step1 raw24532step1Labels = mixedMoment B raw24532step2 raw24532step2Labels := by
      have ha : raw24532step2 = raw24532step1 := by apply Matrix.ext; unfold raw24532step2 raw24532step1; decide +kernel
      have hl : raw24532step1Labels = labelEmbedding1 ∘ raw24532step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24532step1 raw24532step1Labels raw24532step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

def raw24533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24533Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24533step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw24533step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw24533step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24533step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw24533step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24533 raw24533Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw24533 raw24533Labels = mixedMoment B raw24533step0 raw24533step0Labels := by
      have hz : ∀ j, raw24533 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24533step0 = (fun i j => raw24533 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24533step0 raw24533; decide +kernel
      have hl : raw24533step0Labels = raw24533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24533 raw24533Labels permutation265 hz
    mixedMoment B raw24533step0 raw24533step0Labels = mixedMoment B raw24533step1 raw24533step1Labels := by
      have ha : raw24533step1 = (fun i j => raw24533step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24533step1 raw24533step0; decide +kernel
      have hl : raw24533step1Labels = raw24533step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24533step0 raw24533step0Labels permutation34 permutation7
    mixedMoment B raw24533step1 raw24533step1Labels = mixedMoment B raw24533step2 raw24533step2Labels := by
      have ha : raw24533step2 = -raw24533step1 := by apply Matrix.ext; change ∀ i j, raw24533step2 i j = -(raw24533step1 i j); unfold raw24533step2 raw24533step1; decide +kernel
      have hl : raw24533step2Labels = raw24533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24533step2 raw24533step2Labels = mixedMoment B raw24533step3 raw24533step3Labels := by
      have ha : raw24533step3 = raw24533step2 := by apply Matrix.ext; unfold raw24533step3 raw24533step2; decide +kernel
      have hl : raw24533step2Labels = labelEmbedding1 ∘ raw24533step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24533step2 raw24533step2Labels raw24533step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3274 node3274Labels := by rfl

def raw24534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw24534step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24534step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24534step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24534step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24534 raw24534Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw24534 raw24534Labels = mixedMoment B raw24534step0 raw24534step0Labels := by
      have hz : ∀ j, raw24534 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24534step0 = (fun i j => raw24534 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24534step0 raw24534; decide +kernel
      have hl : raw24534step0Labels = raw24534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24534 raw24534Labels permutation265 hz
    mixedMoment B raw24534step0 raw24534step0Labels = mixedMoment B raw24534step1 raw24534step1Labels := by
      have ha : raw24534step1 = (fun i j => raw24534step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24534step1 raw24534step0; decide +kernel
      have hl : raw24534step1Labels = raw24534step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24534step0 raw24534step0Labels permutation44 permutation5
    mixedMoment B raw24534step1 raw24534step1Labels = mixedMoment B raw24534step2 raw24534step2Labels := by
      have ha : raw24534step2 = -raw24534step1 := by apply Matrix.ext; change ∀ i j, raw24534step2 i j = -(raw24534step1 i j); unfold raw24534step2 raw24534step1; decide +kernel
      have hl : raw24534step2Labels = raw24534step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24534step2 raw24534step2Labels = mixedMoment B raw24534step3 raw24534step3Labels := by
      have ha : raw24534step3 = raw24534step2 := by apply Matrix.ext; unfold raw24534step3 raw24534step2; decide +kernel
      have hl : raw24534step2Labels = labelEmbedding1 ∘ raw24534step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24534step2 raw24534step2Labels raw24534step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

def raw24535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24535step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24535step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24535step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24535step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24535step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24535 raw24535Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw24535 raw24535Labels = mixedMoment B raw24535step0 raw24535step0Labels := by
      have hz : ∀ j, raw24535 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24535step0 = (fun i j => raw24535 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24535step0 raw24535; decide +kernel
      have hl : raw24535step0Labels = raw24535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24535 raw24535Labels permutation265 hz
    mixedMoment B raw24535step0 raw24535step0Labels = mixedMoment B raw24535step1 raw24535step1Labels := by
      have ha : raw24535step1 = (fun i j => raw24535step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24535step1 raw24535step0; decide +kernel
      have hl : raw24535step1Labels = raw24535step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24535step0 raw24535step0Labels permutation35 permutation7
    mixedMoment B raw24535step1 raw24535step1Labels = mixedMoment B raw24535step2 raw24535step2Labels := by
      have ha : raw24535step2 = -raw24535step1 := by apply Matrix.ext; change ∀ i j, raw24535step2 i j = -(raw24535step1 i j); unfold raw24535step2 raw24535step1; decide +kernel
      have hl : raw24535step2Labels = raw24535step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24535step2 raw24535step2Labels = mixedMoment B raw24535step3 raw24535step3Labels := by
      have ha : raw24535step3 = raw24535step2 := by apply Matrix.ext; unfold raw24535step3 raw24535step2; decide +kernel
      have hl : raw24535step2Labels = labelEmbedding1 ∘ raw24535step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24535step2 raw24535step2Labels raw24535step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw24536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24536step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24536step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24536step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24536step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24536 raw24536Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw24536 raw24536Labels = mixedMoment B raw24536step0 raw24536step0Labels := by
      have hz : ∀ j, raw24536 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24536step0 = (fun i j => raw24536 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24536step0 raw24536; decide +kernel
      have hl : raw24536step0Labels = raw24536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24536 raw24536Labels permutation265 hz
    mixedMoment B raw24536step0 raw24536step0Labels = mixedMoment B raw24536step1 raw24536step1Labels := by
      have ha : raw24536step1 = (fun i j => raw24536step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24536step1 raw24536step0; decide +kernel
      have hl : raw24536step1Labels = raw24536step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24536step0 raw24536step0Labels permutation38 permutation5
    mixedMoment B raw24536step1 raw24536step1Labels = mixedMoment B raw24536step2 raw24536step2Labels := by
      have ha : raw24536step2 = -raw24536step1 := by apply Matrix.ext; change ∀ i j, raw24536step2 i j = -(raw24536step1 i j); unfold raw24536step2 raw24536step1; decide +kernel
      have hl : raw24536step2Labels = raw24536step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24536step2 raw24536step2Labels = mixedMoment B raw24536step3 raw24536step3Labels := by
      have ha : raw24536step3 = raw24536step2 := by apply Matrix.ext; unfold raw24536step3 raw24536step2; decide +kernel
      have hl : raw24536step2Labels = labelEmbedding1 ∘ raw24536step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24536step2 raw24536step2Labels raw24536step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

def raw24537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24537step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24537step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24537 raw24537Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw24537 raw24537Labels = mixedMoment B raw24537step0 raw24537step0Labels := by
      have ha : raw24537step0 = (fun i j => raw24537 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24537step0 raw24537; decide +kernel
      have hl : raw24537step0Labels = raw24537Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24537 raw24537Labels permutation158 permutation5
    mixedMoment B raw24537step0 raw24537step0Labels = mixedMoment B raw24537step1 raw24537step1Labels := by
      have ha : raw24537step1 = -raw24537step0 := by apply Matrix.ext; change ∀ i j, raw24537step1 i j = -(raw24537step0 i j); unfold raw24537step1 raw24537step0; decide +kernel
      have hl : raw24537step1Labels = raw24537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24537step1 raw24537step1Labels = mixedMoment B raw24537step2 raw24537step2Labels := by
      have ha : raw24537step2 = raw24537step1 := by apply Matrix.ext; unfold raw24537step2 raw24537step1; decide +kernel
      have hl : raw24537step1Labels = labelEmbedding1 ∘ raw24537step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24537step1 raw24537step1Labels raw24537step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

def raw24538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw24538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw24538step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24538step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw24538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24538 raw24538Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw24538 raw24538Labels = mixedMoment B raw24538step0 raw24538step0Labels := by
      have hz : ∀ j, raw24538 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24538step0 = (fun i j => raw24538 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24538step0 raw24538; decide +kernel
      have hl : raw24538step0Labels = raw24538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24538 raw24538Labels permutation265 hz
    mixedMoment B raw24538step0 raw24538step0Labels = mixedMoment B raw24538step1 raw24538step1Labels := by
      have ha : raw24538step1 = (fun i j => raw24538step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24538step1 raw24538step0; decide +kernel
      have hl : raw24538step1Labels = raw24538step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24538step0 raw24538step0Labels permutation32 permutation7
    mixedMoment B raw24538step1 raw24538step1Labels = mixedMoment B raw24538step2 raw24538step2Labels := by
      have ha : raw24538step2 = -raw24538step1 := by apply Matrix.ext; change ∀ i j, raw24538step2 i j = -(raw24538step1 i j); unfold raw24538step2 raw24538step1; decide +kernel
      have hl : raw24538step2Labels = raw24538step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24538step2 raw24538step2Labels = mixedMoment B raw24538step3 raw24538step3Labels := by
      have ha : raw24538step3 = raw24538step2 := by apply Matrix.ext; unfold raw24538step3 raw24538step2; decide +kernel
      have hl : raw24538step2Labels = labelEmbedding1 ∘ raw24538step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24538step2 raw24538step2Labels raw24538step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3274 node3274Labels := by rfl

def raw24539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24539step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw24539step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24539step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24539step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw24539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24539 raw24539Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw24539 raw24539Labels = mixedMoment B raw24539step0 raw24539step0Labels := by
      have hz : ∀ j, raw24539 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24539step0 = (fun i j => raw24539 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24539step0 raw24539; decide +kernel
      have hl : raw24539step0Labels = raw24539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24539 raw24539Labels permutation265 hz
    mixedMoment B raw24539step0 raw24539step0Labels = mixedMoment B raw24539step1 raw24539step1Labels := by
      have ha : raw24539step1 = (fun i j => raw24539step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24539step1 raw24539step0; decide +kernel
      have hl : raw24539step1Labels = raw24539step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24539step0 raw24539step0Labels permutation38 permutation5
    mixedMoment B raw24539step1 raw24539step1Labels = mixedMoment B raw24539step2 raw24539step2Labels := by
      have ha : raw24539step2 = -raw24539step1 := by apply Matrix.ext; change ∀ i j, raw24539step2 i j = -(raw24539step1 i j); unfold raw24539step2 raw24539step1; decide +kernel
      have hl : raw24539step2Labels = raw24539step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24539step2 raw24539step2Labels = mixedMoment B raw24539step3 raw24539step3Labels := by
      have ha : raw24539step3 = raw24539step2 := by apply Matrix.ext; unfold raw24539step3 raw24539step2; decide +kernel
      have hl : raw24539step2Labels = labelEmbedding1 ∘ raw24539step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24539step2 raw24539step2Labels raw24539step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

def raw24540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw24540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw24540step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24540step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24540step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24540 raw24540Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw24540 raw24540Labels = mixedMoment B raw24540step0 raw24540step0Labels := by
      have hz : ∀ j, raw24540 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24540step0 = (fun i j => raw24540 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24540step0 raw24540; decide +kernel
      have hl : raw24540step0Labels = raw24540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24540 raw24540Labels permutation265 hz
    mixedMoment B raw24540step0 raw24540step0Labels = mixedMoment B raw24540step1 raw24540step1Labels := by
      have ha : raw24540step1 = (fun i j => raw24540step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24540step1 raw24540step0; decide +kernel
      have hl : raw24540step1Labels = raw24540step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24540step0 raw24540step0Labels permutation33 permutation7
    mixedMoment B raw24540step1 raw24540step1Labels = mixedMoment B raw24540step2 raw24540step2Labels := by
      have ha : raw24540step2 = -raw24540step1 := by apply Matrix.ext; change ∀ i j, raw24540step2 i j = -(raw24540step1 i j); unfold raw24540step2 raw24540step1; decide +kernel
      have hl : raw24540step2Labels = raw24540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24540step2 raw24540step2Labels = mixedMoment B raw24540step3 raw24540step3Labels := by
      have ha : raw24540step3 = raw24540step2 := by apply Matrix.ext; unfold raw24540step3 raw24540step2; decide +kernel
      have hl : raw24540step2Labels = labelEmbedding1 ∘ raw24540step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24540step2 raw24540step2Labels raw24540step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw24541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24541 raw24541Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw24541 raw24541Labels = mixedMoment B raw24541step0 raw24541step0Labels := by
      have hz : ∀ j, raw24541 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24541step0 = (fun i j => raw24541 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24541step0 raw24541; decide +kernel
      have hl : raw24541step0Labels = raw24541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24541 raw24541Labels permutation265 hz
    mixedMoment B raw24541step0 raw24541step0Labels = mixedMoment B raw24541step1 raw24541step1Labels := by
      have ha : raw24541step1 = (fun i j => raw24541step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24541step1 raw24541step0; decide +kernel
      have hl : raw24541step1Labels = raw24541step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24541step0 raw24541step0Labels permutation40 permutation5
    mixedMoment B raw24541step1 raw24541step1Labels = mixedMoment B raw24541step2 raw24541step2Labels := by
      have ha : raw24541step2 = -raw24541step1 := by apply Matrix.ext; change ∀ i j, raw24541step2 i j = -(raw24541step1 i j); unfold raw24541step2 raw24541step1; decide +kernel
      have hl : raw24541step2Labels = raw24541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24541step2 raw24541step2Labels = mixedMoment B raw24541step3 raw24541step3Labels := by
      have ha : raw24541step3 = raw24541step2 := by apply Matrix.ext; unfold raw24541step3 raw24541step2; decide +kernel
      have hl : raw24541step2Labels = labelEmbedding1 ∘ raw24541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24541step2 raw24541step2Labels raw24541step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

def raw24542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24542step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24542 raw24542Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw24542 raw24542Labels = mixedMoment B raw24542step0 raw24542step0Labels := by
      have ha : raw24542step0 = (fun i j => raw24542 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24542step0 raw24542; decide +kernel
      have hl : raw24542step0Labels = raw24542Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24542 raw24542Labels permutation160 permutation5
    mixedMoment B raw24542step0 raw24542step0Labels = mixedMoment B raw24542step1 raw24542step1Labels := by
      have ha : raw24542step1 = -raw24542step0 := by apply Matrix.ext; change ∀ i j, raw24542step1 i j = -(raw24542step0 i j); unfold raw24542step1 raw24542step0; decide +kernel
      have hl : raw24542step1Labels = raw24542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24542step1 raw24542step1Labels = mixedMoment B raw24542step2 raw24542step2Labels := by
      have ha : raw24542step2 = raw24542step1 := by apply Matrix.ext; unfold raw24542step2 raw24542step1; decide +kernel
      have hl : raw24542step1Labels = labelEmbedding1 ∘ raw24542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24542step1 raw24542step1Labels raw24542step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

def raw24543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw24543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw24543step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24543step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw24543step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24543 raw24543Labels = mixedMoment B node3273 node3273Labels := by
  calc
    mixedMoment B raw24543 raw24543Labels = mixedMoment B raw24543step0 raw24543step0Labels := by
      have hz : ∀ j, raw24543 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24543step0 = (fun i j => raw24543 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24543step0 raw24543; decide +kernel
      have hl : raw24543step0Labels = raw24543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24543 raw24543Labels permutation265 hz
    mixedMoment B raw24543step0 raw24543step0Labels = mixedMoment B raw24543step1 raw24543step1Labels := by
      have ha : raw24543step1 = (fun i j => raw24543step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24543step1 raw24543step0; decide +kernel
      have hl : raw24543step1Labels = raw24543step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24543step0 raw24543step0Labels permutation32 permutation7
    mixedMoment B raw24543step1 raw24543step1Labels = mixedMoment B raw24543step2 raw24543step2Labels := by
      have ha : raw24543step2 = -raw24543step1 := by apply Matrix.ext; change ∀ i j, raw24543step2 i j = -(raw24543step1 i j); unfold raw24543step2 raw24543step1; decide +kernel
      have hl : raw24543step2Labels = raw24543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24543step2 raw24543step2Labels = mixedMoment B raw24543step3 raw24543step3Labels := by
      have ha : raw24543step3 = raw24543step2 := by apply Matrix.ext; unfold raw24543step3 raw24543step2; decide +kernel
      have hl : raw24543step2Labels = labelEmbedding1 ∘ raw24543step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24543step2 raw24543step2Labels raw24543step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3273 node3273Labels := by rfl

def raw24544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24544step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24544step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24544step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24544 raw24544Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw24544 raw24544Labels = mixedMoment B raw24544step0 raw24544step0Labels := by
      have hz : ∀ j, raw24544 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24544step0 = (fun i j => raw24544 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24544step0 raw24544; decide +kernel
      have hl : raw24544step0Labels = raw24544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24544 raw24544Labels permutation265 hz
    mixedMoment B raw24544step0 raw24544step0Labels = mixedMoment B raw24544step1 raw24544step1Labels := by
      have ha : raw24544step1 = (fun i j => raw24544step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24544step1 raw24544step0; decide +kernel
      have hl : raw24544step1Labels = raw24544step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24544step0 raw24544step0Labels permutation40 permutation5
    mixedMoment B raw24544step1 raw24544step1Labels = mixedMoment B raw24544step2 raw24544step2Labels := by
      have ha : raw24544step2 = -raw24544step1 := by apply Matrix.ext; change ∀ i j, raw24544step2 i j = -(raw24544step1 i j); unfold raw24544step2 raw24544step1; decide +kernel
      have hl : raw24544step2Labels = raw24544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24544step2 raw24544step2Labels = mixedMoment B raw24544step3 raw24544step3Labels := by
      have ha : raw24544step3 = raw24544step2 := by apply Matrix.ext; unfold raw24544step3 raw24544step2; decide +kernel
      have hl : raw24544step2Labels = labelEmbedding1 ∘ raw24544step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24544step2 raw24544step2Labels raw24544step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw24545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw24545step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24545step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24545 raw24545Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw24545 raw24545Labels = mixedMoment B raw24545step0 raw24545step0Labels := by
      have hz : ∀ j, raw24545 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24545step0 = (fun i j => raw24545 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24545step0 raw24545; decide +kernel
      have hl : raw24545step0Labels = raw24545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24545 raw24545Labels permutation265 hz
    mixedMoment B raw24545step0 raw24545step0Labels = mixedMoment B raw24545step1 raw24545step1Labels := by
      have ha : raw24545step1 = (fun i j => raw24545step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24545step1 raw24545step0; decide +kernel
      have hl : raw24545step1Labels = raw24545step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24545step0 raw24545step0Labels permutation46 permutation5
    mixedMoment B raw24545step1 raw24545step1Labels = mixedMoment B raw24545step2 raw24545step2Labels := by
      have ha : raw24545step2 = -raw24545step1 := by apply Matrix.ext; change ∀ i j, raw24545step2 i j = -(raw24545step1 i j); unfold raw24545step2 raw24545step1; decide +kernel
      have hl : raw24545step2Labels = raw24545step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24545step2 raw24545step2Labels = mixedMoment B raw24545step3 raw24545step3Labels := by
      have ha : raw24545step3 = raw24545step2 := by apply Matrix.ext; unfold raw24545step3 raw24545step2; decide +kernel
      have hl : raw24545step2Labels = labelEmbedding1 ∘ raw24545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24545step2 raw24545step2Labels raw24545step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw24546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24546 raw24546Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24546 raw24546Labels = mixedMoment B raw24546step0 raw24546step0Labels := by
      have hz : ∀ j, raw24546 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24546step0 = (fun i j => raw24546 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24546step0 raw24546; decide +kernel
      have hl : raw24546step0Labels = raw24546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24546 raw24546Labels permutation265 hz
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw24547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24547 raw24547Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw24547 raw24547Labels = mixedMoment B raw24547step0 raw24547step0Labels := by
      have ha : raw24547step0 = (fun i j => raw24547 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24547step0 raw24547; decide +kernel
      have hl : raw24547step0Labels = raw24547Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24547 raw24547Labels permutation176 permutation2
    _ = mixedMoment B node625 node625Labels := by rfl

def raw24548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24548 raw24548Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw24548 raw24548Labels = mixedMoment B raw24548step0 raw24548step0Labels := by
      have hz : ∀ j, raw24548 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24548step0 = (fun i j => raw24548 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24548step0 raw24548; decide +kernel
      have hl : raw24548step0Labels = raw24548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24548 raw24548Labels permutation265 hz
    _ = mixedMoment B node640 node640Labels := by rfl

def raw24549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24549 raw24549Labels = mixedMoment B node632 node632Labels := by
  calc
    mixedMoment B raw24549 raw24549Labels = mixedMoment B raw24549step0 raw24549step0Labels := by
      have hz : ∀ j, raw24549 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24549step0 = (fun i j => raw24549 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24549step0 raw24549; decide +kernel
      have hl : raw24549step0Labels = raw24549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24549 raw24549Labels permutation265 hz
    mixedMoment B raw24549step0 raw24549step0Labels = mixedMoment B raw24549step1 raw24549step1Labels := by
      have ha : raw24549step1 = (fun i j => raw24549step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24549step1 raw24549step0; decide +kernel
      have hl : raw24549step1Labels = raw24549step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24549step0 raw24549step0Labels permutation34 permutation2
    _ = mixedMoment B node632 node632Labels := by rfl

def raw24550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24550 raw24550Labels = mixedMoment B node632 node632Labels := by
  calc
    mixedMoment B raw24550 raw24550Labels = mixedMoment B raw24550step0 raw24550step0Labels := by
      have hz : ∀ j, raw24550 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24550step0 = (fun i j => raw24550 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24550step0 raw24550; decide +kernel
      have hl : raw24550step0Labels = raw24550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24550 raw24550Labels permutation265 hz
    _ = mixedMoment B node632 node632Labels := by rfl

def raw24551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24551 raw24551Labels = mixedMoment B node630 node630Labels := by
  calc
    mixedMoment B raw24551 raw24551Labels = mixedMoment B raw24551step0 raw24551step0Labels := by
      have hz : ∀ j, raw24551 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24551step0 = (fun i j => raw24551 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24551step0 raw24551; decide +kernel
      have hl : raw24551step0Labels = raw24551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24551 raw24551Labels permutation265 hz
    _ = mixedMoment B node630 node630Labels := by rfl

def raw24552 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw24552Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24552step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw24552step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24552 raw24552Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw24552 raw24552Labels = mixedMoment B raw24552step0 raw24552step0Labels := by
      have hz : ∀ j, raw24552 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24552step0 = (fun i j => raw24552 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24552step0 raw24552; decide +kernel
      have hl : raw24552step0Labels = raw24552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24552 raw24552Labels permutation265 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw24553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24553 raw24553Labels = mixedMoment B node2556 node2556Labels := by
  calc
    _ = mixedMoment B node2556 node2556Labels := by rfl

def raw24554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24554 raw24554Labels = mixedMoment B node1158 node1158Labels := by
  calc
    _ = mixedMoment B node1158 node1158Labels := by rfl

def raw24555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24555 raw24555Labels = mixedMoment B node1152 node1152Labels := by
  calc
    mixedMoment B raw24555 raw24555Labels = mixedMoment B raw24555step0 raw24555step0Labels := by
      have ha : raw24555step0 = (fun i j => raw24555 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24555step0 raw24555; decide +kernel
      have hl : raw24555step0Labels = raw24555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24555 raw24555Labels permutation154 permutation2
    _ = mixedMoment B node1152 node1152Labels := by rfl

def raw24556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw24556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24556 raw24556Labels = mixedMoment B node1152 node1152Labels := by
  calc
    _ = mixedMoment B node1152 node1152Labels := by rfl

def raw24557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24557 raw24557Labels = mixedMoment B node1150 node1150Labels := by
  calc
    _ = mixedMoment B node1150 node1150Labels := by rfl

def raw24558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24558step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24558 raw24558Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw24558 raw24558Labels = mixedMoment B raw24558step0 raw24558step0Labels := by
      have ha : raw24558step0 = (fun i j => raw24558 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24558step0 raw24558; decide +kernel
      have hl : raw24558step0Labels = raw24558Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24558 raw24558Labels permutation176 permutation3
    mixedMoment B raw24558step0 raw24558step0Labels = mixedMoment B raw24558step1 raw24558step1Labels := by
      have ha : raw24558step1 = raw24558step0 := by apply Matrix.ext; unfold raw24558step1 raw24558step0; decide +kernel
      have hl : raw24558step0Labels = labelEmbedding6 ∘ raw24558step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24558step0 raw24558step0Labels raw24558step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4143 node4143Labels := by rfl

def raw24559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24559step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24559 raw24559Labels = mixedMoment B node4516 node4516Labels := by
  calc
    mixedMoment B raw24559 raw24559Labels = mixedMoment B raw24559step0 raw24559step0Labels := by
      have ha : raw24559step0 = (fun i j => raw24559 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24559step0 raw24559; decide +kernel
      have hl : raw24559step0Labels = raw24559Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24559 raw24559Labels permutation176 permutation3
    mixedMoment B raw24559step0 raw24559step0Labels = mixedMoment B raw24559step1 raw24559step1Labels := by
      have ha : raw24559step1 = raw24559step0 := by apply Matrix.ext; unfold raw24559step1 raw24559step0; decide +kernel
      have hl : raw24559step0Labels = labelEmbedding6 ∘ raw24559step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24559step0 raw24559step0Labels raw24559step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4516 node4516Labels := by rfl

def raw24560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24560step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24560step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24560 raw24560Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24560 raw24560Labels = mixedMoment B raw24560step0 raw24560step0Labels := by
      have hz : ∀ j, raw24560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24560step0 = (fun i j => raw24560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24560step0 raw24560; decide +kernel
      have hl : raw24560step0Labels = raw24560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24560 raw24560Labels permutation434 hz
    mixedMoment B raw24560step0 raw24560step0Labels = mixedMoment B raw24560step1 raw24560step1Labels := by
      have ha : raw24560step1 = (fun i j => raw24560step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24560step1 raw24560step0; decide +kernel
      have hl : raw24560step1Labels = raw24560step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24560step0 raw24560step0Labels permutation38 permutation3
    mixedMoment B raw24560step1 raw24560step1Labels = mixedMoment B raw24560step2 raw24560step2Labels := by
      have ha : raw24560step2 = raw24560step1 := by apply Matrix.ext; unfold raw24560step2 raw24560step1; decide +kernel
      have hl : raw24560step1Labels = labelEmbedding6 ∘ raw24560step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24560step1 raw24560step1Labels raw24560step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw24561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24561step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24561 raw24561Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24561 raw24561Labels = mixedMoment B raw24561step0 raw24561step0Labels := by
      have hz : ∀ j, raw24561 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24561step0 = (fun i j => raw24561 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24561step0 raw24561; decide +kernel
      have hl : raw24561step0Labels = raw24561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24561 raw24561Labels permutation520 hz
    mixedMoment B raw24561step0 raw24561step0Labels = mixedMoment B raw24561step1 raw24561step1Labels := by
      have ha : raw24561step1 = (fun i j => raw24561step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24561step1 raw24561step0; decide +kernel
      have hl : raw24561step1Labels = raw24561step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24561step0 raw24561step0Labels permutation38 permutation3
    mixedMoment B raw24561step1 raw24561step1Labels = mixedMoment B raw24561step2 raw24561step2Labels := by
      have ha : raw24561step2 = raw24561step1 := by apply Matrix.ext; unfold raw24561step2 raw24561step1; decide +kernel
      have hl : raw24561step1Labels = labelEmbedding6 ∘ raw24561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24561step1 raw24561step1Labels raw24561step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw24562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24562step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24562step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24562 raw24562Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw24562 raw24562Labels = mixedMoment B raw24562step0 raw24562step0Labels := by
      have hz : ∀ j, raw24562 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24562step0 = (fun i j => raw24562 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24562step0 raw24562; decide +kernel
      have hl : raw24562step0Labels = raw24562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24562 raw24562Labels permutation265 hz
    mixedMoment B raw24562step0 raw24562step0Labels = mixedMoment B raw24562step1 raw24562step1Labels := by
      have ha : raw24562step1 = (fun i j => raw24562step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24562step1 raw24562step0; decide +kernel
      have hl : raw24562step1Labels = raw24562step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24562step0 raw24562step0Labels permutation32 permutation3
    mixedMoment B raw24562step1 raw24562step1Labels = mixedMoment B raw24562step2 raw24562step2Labels := by
      have ha : raw24562step2 = raw24562step1 := by apply Matrix.ext; unfold raw24562step2 raw24562step1; decide +kernel
      have hl : raw24562step1Labels = labelEmbedding6 ∘ raw24562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24562step1 raw24562step1Labels raw24562step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw24563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24563step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24563 raw24563Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw24563 raw24563Labels = mixedMoment B raw24563step0 raw24563step0Labels := by
      have ha : raw24563step0 = (fun i j => raw24563 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24563step0 raw24563; decide +kernel
      have hl : raw24563step0Labels = raw24563Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24563 raw24563Labels permutation152 permutation3
    mixedMoment B raw24563step0 raw24563step0Labels = mixedMoment B raw24563step1 raw24563step1Labels := by
      have ha : raw24563step1 = raw24563step0 := by apply Matrix.ext; unfold raw24563step1 raw24563step0; decide +kernel
      have hl : raw24563step0Labels = labelEmbedding6 ∘ raw24563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24563step0 raw24563step0Labels raw24563step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4544 node4544Labels := by rfl

def raw24564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24564 raw24564Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw24564 raw24564Labels = mixedMoment B raw24564step0 raw24564step0Labels := by
      have hz : ∀ j, raw24564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24564step0 = (fun i j => raw24564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24564step0 raw24564; decide +kernel
      have hl : raw24564step0Labels = raw24564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24564 raw24564Labels permutation434 hz
    mixedMoment B raw24564step0 raw24564step0Labels = mixedMoment B raw24564step1 raw24564step1Labels := by
      have hz : ∀ j, raw24564step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24564step1 = (fun i j => raw24564step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24564step1 raw24564step0; decide +kernel
      have hl : raw24564step1Labels = raw24564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24564step0 raw24564step0Labels permutation56 hz
    mixedMoment B raw24564step1 raw24564step1Labels = mixedMoment B raw24564step2 raw24564step2Labels := by
      have ha : raw24564step2 = (fun i j => raw24564step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24564step2 raw24564step1; decide +kernel
      have hl : raw24564step2Labels = raw24564step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24564step1 raw24564step1Labels permutation10 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw24565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24565 raw24565Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw24565 raw24565Labels = mixedMoment B raw24565step0 raw24565step0Labels := by
      have hz : ∀ j, raw24565 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24565step0 = (fun i j => raw24565 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24565step0 raw24565; decide +kernel
      have hl : raw24565step0Labels = raw24565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24565 raw24565Labels permutation520 hz
    mixedMoment B raw24565step0 raw24565step0Labels = mixedMoment B raw24565step1 raw24565step1Labels := by
      have hz : ∀ j, raw24565step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24565step1 = (fun i j => raw24565step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24565step1 raw24565step0; decide +kernel
      have hl : raw24565step1Labels = raw24565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24565step0 raw24565step0Labels permutation56 hz
    mixedMoment B raw24565step1 raw24565step1Labels = mixedMoment B raw24565step2 raw24565step2Labels := by
      have ha : raw24565step2 = (fun i j => raw24565step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24565step2 raw24565step1; decide +kernel
      have hl : raw24565step2Labels = raw24565step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24565step1 raw24565step1Labels permutation10 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw24566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24566step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24566step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24566 raw24566Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw24566 raw24566Labels = mixedMoment B raw24566step0 raw24566step0Labels := by
      have hz : ∀ j, raw24566 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24566step0 = (fun i j => raw24566 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24566step0 raw24566; decide +kernel
      have hl : raw24566step0Labels = raw24566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24566 raw24566Labels permutation265 hz
    mixedMoment B raw24566step0 raw24566step0Labels = mixedMoment B raw24566step1 raw24566step1Labels := by
      have ha : raw24566step1 = (fun i j => raw24566step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24566step1 raw24566step0; decide +kernel
      have hl : raw24566step1Labels = raw24566step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24566step0 raw24566step0Labels permutation35 permutation3
    mixedMoment B raw24566step1 raw24566step1Labels = mixedMoment B raw24566step2 raw24566step2Labels := by
      have ha : raw24566step2 = raw24566step1 := by apply Matrix.ext; unfold raw24566step2 raw24566step1; decide +kernel
      have hl : raw24566step1Labels = labelEmbedding6 ∘ raw24566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24566step1 raw24566step1Labels raw24566step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

def raw24567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24567step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24567 raw24567Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw24567 raw24567Labels = mixedMoment B raw24567step0 raw24567step0Labels := by
      have ha : raw24567step0 = (fun i j => raw24567 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24567step0 raw24567; decide +kernel
      have hl : raw24567step0Labels = raw24567Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24567 raw24567Labels permutation155 permutation3
    mixedMoment B raw24567step0 raw24567step0Labels = mixedMoment B raw24567step1 raw24567step1Labels := by
      have ha : raw24567step1 = raw24567step0 := by apply Matrix.ext; unfold raw24567step1 raw24567step0; decide +kernel
      have hl : raw24567step0Labels = labelEmbedding6 ∘ raw24567step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24567step0 raw24567step0Labels raw24567step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

def raw24568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24568step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24568 raw24568Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw24568 raw24568Labels = mixedMoment B raw24568step0 raw24568step0Labels := by
      have hz : ∀ j, raw24568 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24568step0 = (fun i j => raw24568 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24568step0 raw24568; decide +kernel
      have hl : raw24568step0Labels = raw24568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24568 raw24568Labels permutation265 hz
    mixedMoment B raw24568step0 raw24568step0Labels = mixedMoment B raw24568step1 raw24568step1Labels := by
      have ha : raw24568step1 = (fun i j => raw24568step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24568step1 raw24568step0; decide +kernel
      have hl : raw24568step1Labels = raw24568step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24568step0 raw24568step0Labels permutation35 permutation3
    mixedMoment B raw24568step1 raw24568step1Labels = mixedMoment B raw24568step2 raw24568step2Labels := by
      have ha : raw24568step2 = raw24568step1 := by apply Matrix.ext; unfold raw24568step2 raw24568step1; decide +kernel
      have hl : raw24568step1Labels = labelEmbedding6 ∘ raw24568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24568step1 raw24568step1Labels raw24568step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

def raw24569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24569step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24569 raw24569Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24569 raw24569Labels = mixedMoment B raw24569step0 raw24569step0Labels := by
      have hz : ∀ j, raw24569 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24569step0 = (fun i j => raw24569 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24569step0 raw24569; decide +kernel
      have hl : raw24569step0Labels = raw24569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24569 raw24569Labels permutation520 hz
    mixedMoment B raw24569step0 raw24569step0Labels = mixedMoment B raw24569step1 raw24569step1Labels := by
      have hz : ∀ j, raw24569step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24569step1 = (fun i j => raw24569step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24569step1 raw24569step0; decide +kernel
      have hl : raw24569step1Labels = raw24569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24569step0 raw24569step0Labels permutation56 hz
    mixedMoment B raw24569step1 raw24569step1Labels = mixedMoment B raw24569step2 raw24569step2Labels := by
      have ha : raw24569step2 = (fun i j => raw24569step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24569step2 raw24569step1; decide +kernel
      have hl : raw24569step2Labels = raw24569step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24569step1 raw24569step1Labels permutation9 permutation3
    mixedMoment B raw24569step2 raw24569step2Labels = mixedMoment B raw24569step3 raw24569step3Labels := by
      have ha : raw24569step3 = raw24569step2 := by apply Matrix.ext; unfold raw24569step3 raw24569step2; decide +kernel
      have hl : raw24569step2Labels = labelEmbedding6 ∘ raw24569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24569step2 raw24569step2Labels raw24569step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw24570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24570step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24570 raw24570Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw24570 raw24570Labels = mixedMoment B raw24570step0 raw24570step0Labels := by
      have hz : ∀ j, raw24570 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24570step0 = (fun i j => raw24570 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24570step0 raw24570; decide +kernel
      have hl : raw24570step0Labels = raw24570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24570 raw24570Labels permutation265 hz
    mixedMoment B raw24570step0 raw24570step0Labels = mixedMoment B raw24570step1 raw24570step1Labels := by
      have ha : raw24570step1 = (fun i j => raw24570step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24570step1 raw24570step0; decide +kernel
      have hl : raw24570step1Labels = raw24570step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24570step0 raw24570step0Labels permutation33 permutation3
    mixedMoment B raw24570step1 raw24570step1Labels = mixedMoment B raw24570step2 raw24570step2Labels := by
      have ha : raw24570step2 = raw24570step1 := by apply Matrix.ext; unfold raw24570step2 raw24570step1; decide +kernel
      have hl : raw24570step1Labels = labelEmbedding6 ∘ raw24570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24570step1 raw24570step1Labels raw24570step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

def raw24571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24571step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24571 raw24571Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw24571 raw24571Labels = mixedMoment B raw24571step0 raw24571step0Labels := by
      have ha : raw24571step0 = (fun i j => raw24571 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24571step0 raw24571; decide +kernel
      have hl : raw24571step0Labels = raw24571Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24571 raw24571Labels permutation153 permutation3
    mixedMoment B raw24571step0 raw24571step0Labels = mixedMoment B raw24571step1 raw24571step1Labels := by
      have ha : raw24571step1 = raw24571step0 := by apply Matrix.ext; unfold raw24571step1 raw24571step0; decide +kernel
      have hl : raw24571step0Labels = labelEmbedding6 ∘ raw24571step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24571step0 raw24571step0Labels raw24571step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

def raw24572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24572step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24572 raw24572Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw24572 raw24572Labels = mixedMoment B raw24572step0 raw24572step0Labels := by
      have hz : ∀ j, raw24572 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24572step0 = (fun i j => raw24572 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24572step0 raw24572; decide +kernel
      have hl : raw24572step0Labels = raw24572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24572 raw24572Labels permutation265 hz
    mixedMoment B raw24572step0 raw24572step0Labels = mixedMoment B raw24572step1 raw24572step1Labels := by
      have ha : raw24572step1 = (fun i j => raw24572step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24572step1 raw24572step0; decide +kernel
      have hl : raw24572step1Labels = raw24572step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24572step0 raw24572step0Labels permutation33 permutation3
    mixedMoment B raw24572step1 raw24572step1Labels = mixedMoment B raw24572step2 raw24572step2Labels := by
      have ha : raw24572step2 = raw24572step1 := by apply Matrix.ext; unfold raw24572step2 raw24572step1; decide +kernel
      have hl : raw24572step1Labels = labelEmbedding6 ∘ raw24572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24572step1 raw24572step1Labels raw24572step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

def raw24573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24573step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24573step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24573 raw24573Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24573 raw24573Labels = mixedMoment B raw24573step0 raw24573step0Labels := by
      have hz : ∀ j, raw24573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24573step0 = (fun i j => raw24573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24573step0 raw24573; decide +kernel
      have hl : raw24573step0Labels = raw24573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24573 raw24573Labels permutation434 hz
    mixedMoment B raw24573step0 raw24573step0Labels = mixedMoment B raw24573step1 raw24573step1Labels := by
      have hz : ∀ j, raw24573step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24573step1 = (fun i j => raw24573step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24573step1 raw24573step0; decide +kernel
      have hl : raw24573step1Labels = raw24573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24573step0 raw24573step0Labels permutation56 hz
    mixedMoment B raw24573step1 raw24573step1Labels = mixedMoment B raw24573step2 raw24573step2Labels := by
      have ha : raw24573step2 = (fun i j => raw24573step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24573step2 raw24573step1; decide +kernel
      have hl : raw24573step2Labels = raw24573step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24573step1 raw24573step1Labels permutation9 permutation3
    mixedMoment B raw24573step2 raw24573step2Labels = mixedMoment B raw24573step3 raw24573step3Labels := by
      have ha : raw24573step3 = raw24573step2 := by apply Matrix.ext; unfold raw24573step3 raw24573step2; decide +kernel
      have hl : raw24573step2Labels = labelEmbedding6 ∘ raw24573step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24573step2 raw24573step2Labels raw24573step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw24574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24574step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24574 raw24574Labels = mixedMoment B node4144 node4144Labels := by
  calc
    mixedMoment B raw24574 raw24574Labels = mixedMoment B raw24574step0 raw24574step0Labels := by
      have hz : ∀ j, raw24574 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24574step0 = (fun i j => raw24574 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24574step0 raw24574; decide +kernel
      have hl : raw24574step0Labels = raw24574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24574 raw24574Labels permutation265 hz
    mixedMoment B raw24574step0 raw24574step0Labels = mixedMoment B raw24574step1 raw24574step1Labels := by
      have ha : raw24574step1 = (fun i j => raw24574step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24574step1 raw24574step0; decide +kernel
      have hl : raw24574step1Labels = raw24574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24574step0 raw24574step0Labels permutation32 permutation3
    mixedMoment B raw24574step1 raw24574step1Labels = mixedMoment B raw24574step2 raw24574step2Labels := by
      have ha : raw24574step2 = raw24574step1 := by apply Matrix.ext; unfold raw24574step2 raw24574step1; decide +kernel
      have hl : raw24574step1Labels = labelEmbedding6 ∘ raw24574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24574step1 raw24574step1Labels raw24574step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4144 node4144Labels := by rfl

def raw24575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24575step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24575 raw24575Labels = mixedMoment B node4523 node4523Labels := by
  calc
    mixedMoment B raw24575 raw24575Labels = mixedMoment B raw24575step0 raw24575step0Labels := by
      have ha : raw24575step0 = (fun i j => raw24575 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24575step0 raw24575; decide +kernel
      have hl : raw24575step0Labels = raw24575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24575 raw24575Labels permutation152 permutation3
    mixedMoment B raw24575step0 raw24575step0Labels = mixedMoment B raw24575step1 raw24575step1Labels := by
      have ha : raw24575step1 = raw24575step0 := by apply Matrix.ext; unfold raw24575step1 raw24575step0; decide +kernel
      have hl : raw24575step0Labels = labelEmbedding6 ∘ raw24575step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24575step0 raw24575step0Labels raw24575step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4523 node4523Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
