import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10368 raw10368Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw10368 raw10368Labels = mixedMoment B raw10368step0 raw10368step0Labels := by
      have hz : ∀ j, raw10368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10368step0 = (fun i j => raw10368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10368step0 raw10368; decide +kernel
      have hl : raw10368step0Labels = raw10368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10368 raw10368Labels permutation346 hz
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw10369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10369step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10369 raw10369Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw10369 raw10369Labels = mixedMoment B raw10369step0 raw10369step0Labels := by
      have hz : ∀ j, raw10369 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10369step0 = (fun i j => raw10369 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10369step0 raw10369; decide +kernel
      have hl : raw10369step0Labels = raw10369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10369 raw10369Labels permutation265 hz
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw10370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10370step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10370 raw10370Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw10370 raw10370Labels = mixedMoment B raw10370step0 raw10370step0Labels := by
      have hz : ∀ j, raw10370 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10370step0 = (fun i j => raw10370 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10370step0 raw10370; decide +kernel
      have hl : raw10370step0Labels = raw10370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10370 raw10370Labels permutation346 hz
    mixedMoment B raw10370step0 raw10370step0Labels = mixedMoment B raw10370step1 raw10370step1Labels := by
      have hz : ∀ j, raw10370step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10370step1 = (fun i j => raw10370step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10370step1 raw10370step0; decide +kernel
      have hl : raw10370step1Labels = raw10370step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10370step0 raw10370step0Labels permutation56 hz
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw10371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10371step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10371 raw10371Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw10371 raw10371Labels = mixedMoment B raw10371step0 raw10371step0Labels := by
      have hz : ∀ j, raw10371 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10371step0 = (fun i j => raw10371 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10371step0 raw10371; decide +kernel
      have hl : raw10371step0Labels = raw10371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10371 raw10371Labels permutation346 hz
    mixedMoment B raw10371step0 raw10371step0Labels = mixedMoment B raw10371step1 raw10371step1Labels := by
      have hz : ∀ j, raw10371step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10371step1 = (fun i j => raw10371step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10371step1 raw10371step0; decide +kernel
      have hl : raw10371step1Labels = raw10371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10371step0 raw10371step0Labels permutation56 hz
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw10372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw10372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10372 raw10372Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw10372 raw10372Labels = mixedMoment B raw10372step0 raw10372step0Labels := by
      have hz : ∀ j, raw10372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10372step0 = (fun i j => raw10372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10372step0 raw10372; decide +kernel
      have hl : raw10372step0Labels = raw10372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10372 raw10372Labels permutation346 hz
    mixedMoment B raw10372step0 raw10372step0Labels = mixedMoment B raw10372step1 raw10372step1Labels := by
      have ha : raw10372step1 = (fun i j => raw10372step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10372step1 raw10372step0; decide +kernel
      have hl : raw10372step1Labels = raw10372step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10372step0 raw10372step0Labels permutation151 permutation3
    mixedMoment B raw10372step1 raw10372step1Labels = mixedMoment B raw10372step2 raw10372step2Labels := by
      have ha : raw10372step2 = -raw10372step1 := by apply Matrix.ext; change ∀ i j, raw10372step2 i j = -(raw10372step1 i j); unfold raw10372step2 raw10372step1; decide +kernel
      have hl : raw10372step2Labels = raw10372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw10373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw10373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10373 raw10373Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw10373 raw10373Labels = mixedMoment B raw10373step0 raw10373step0Labels := by
      have hz : ∀ j, raw10373 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10373step0 = (fun i j => raw10373 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10373step0 raw10373; decide +kernel
      have hl : raw10373step0Labels = raw10373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10373 raw10373Labels permutation265 hz
    mixedMoment B raw10373step0 raw10373step0Labels = mixedMoment B raw10373step1 raw10373step1Labels := by
      have ha : raw10373step1 = (fun i j => raw10373step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10373step1 raw10373step0; decide +kernel
      have hl : raw10373step1Labels = raw10373step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10373step0 raw10373step0Labels permutation151 permutation3
    mixedMoment B raw10373step1 raw10373step1Labels = mixedMoment B raw10373step2 raw10373step2Labels := by
      have ha : raw10373step2 = -raw10373step1 := by apply Matrix.ext; change ∀ i j, raw10373step2 i j = -(raw10373step1 i j); unfold raw10373step2 raw10373step1; decide +kernel
      have hl : raw10373step2Labels = raw10373step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw10374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw10374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10374step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10374 raw10374Labels = mixedMoment B node4006 node4006Labels := by
  calc
    mixedMoment B raw10374 raw10374Labels = mixedMoment B raw10374step0 raw10374step0Labels := by
      have hz : ∀ j, raw10374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10374step0 = (fun i j => raw10374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10374step0 raw10374; decide +kernel
      have hl : raw10374step0Labels = raw10374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10374 raw10374Labels permutation346 hz
    mixedMoment B raw10374step0 raw10374step0Labels = mixedMoment B raw10374step1 raw10374step1Labels := by
      have hz : ∀ j, raw10374step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10374step1 = (fun i j => raw10374step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10374step1 raw10374step0; decide +kernel
      have hl : raw10374step1Labels = raw10374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10374step0 raw10374step0Labels permutation56 hz
    mixedMoment B raw10374step1 raw10374step1Labels = mixedMoment B raw10374step2 raw10374step2Labels := by
      have ha : raw10374step2 = (fun i j => raw10374step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10374step2 raw10374step1; decide +kernel
      have hl : raw10374step2Labels = raw10374step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10374step1 raw10374step1Labels permutation31 permutation3
    mixedMoment B raw10374step2 raw10374step2Labels = mixedMoment B raw10374step3 raw10374step3Labels := by
      have ha : raw10374step3 = -raw10374step2 := by apply Matrix.ext; change ∀ i j, raw10374step3 i j = -(raw10374step2 i j); unfold raw10374step3 raw10374step2; decide +kernel
      have hl : raw10374step3Labels = raw10374step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4006 node4006Labels := by rfl

def raw10375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10375 raw10375Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw10375 raw10375Labels = mixedMoment B raw10375step0 raw10375step0Labels := by
      have hz : ∀ j, raw10375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10375step0 = (fun i j => raw10375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10375step0 raw10375; decide +kernel
      have hl : raw10375step0Labels = raw10375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10375 raw10375Labels permutation346 hz
    mixedMoment B raw10375step0 raw10375step0Labels = mixedMoment B raw10375step1 raw10375step1Labels := by
      have hz : ∀ j, raw10375step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10375step1 = (fun i j => raw10375step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10375step1 raw10375step0; decide +kernel
      have hl : raw10375step1Labels = raw10375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10375step0 raw10375step0Labels permutation56 hz
    mixedMoment B raw10375step1 raw10375step1Labels = mixedMoment B raw10375step2 raw10375step2Labels := by
      have ha : raw10375step2 = (fun i j => raw10375step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10375step2 raw10375step1; decide +kernel
      have hl : raw10375step2Labels = raw10375step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10375step1 raw10375step1Labels permutation25 permutation6
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw10376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10376step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10376 raw10376Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw10376 raw10376Labels = mixedMoment B raw10376step0 raw10376step0Labels := by
      have hz : ∀ j, raw10376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10376step0 = (fun i j => raw10376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10376step0 raw10376; decide +kernel
      have hl : raw10376step0Labels = raw10376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10376 raw10376Labels permutation346 hz
    mixedMoment B raw10376step0 raw10376step0Labels = mixedMoment B raw10376step1 raw10376step1Labels := by
      have hz : ∀ j, raw10376step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10376step1 = (fun i j => raw10376step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10376step1 raw10376step0; decide +kernel
      have hl : raw10376step1Labels = raw10376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10376step0 raw10376step0Labels permutation56 hz
    mixedMoment B raw10376step1 raw10376step1Labels = mixedMoment B raw10376step2 raw10376step2Labels := by
      have ha : raw10376step2 = (fun i j => raw10376step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10376step2 raw10376step1; decide +kernel
      have hl : raw10376step2Labels = raw10376step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10376step1 raw10376step1Labels permutation25 permutation6
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw10377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10377 raw10377Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw10377 raw10377Labels = mixedMoment B raw10377step0 raw10377step0Labels := by
      have hz : ∀ j, raw10377 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10377step0 = (fun i j => raw10377 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10377step0 raw10377; decide +kernel
      have hl : raw10377step0Labels = raw10377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10377 raw10377Labels permutation346 hz
    mixedMoment B raw10377step0 raw10377step0Labels = mixedMoment B raw10377step1 raw10377step1Labels := by
      have ha : raw10377step1 = (fun i j => raw10377step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10377step1 raw10377step0; decide +kernel
      have hl : raw10377step1Labels = raw10377step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10377step0 raw10377step0Labels permutation40 permutation3
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw10378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10378 raw10378Labels = mixedMoment B node2934 node2934Labels := by
  calc
    mixedMoment B raw10378 raw10378Labels = mixedMoment B raw10378step0 raw10378step0Labels := by
      have ha : raw10378step0 = (fun i j => raw10378 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10378step0 raw10378; decide +kernel
      have hl : raw10378step0Labels = raw10378Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10378 raw10378Labels permutation184 permutation3
    _ = mixedMoment B node2934 node2934Labels := by rfl

def raw10379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10379 raw10379Labels = mixedMoment B node2998 node2998Labels := by
  calc
    mixedMoment B raw10379 raw10379Labels = mixedMoment B raw10379step0 raw10379step0Labels := by
      have hz : ∀ j, raw10379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10379step0 = (fun i j => raw10379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10379step0 raw10379; decide +kernel
      have hl : raw10379step0Labels = raw10379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10379 raw10379Labels permutation346 hz
    mixedMoment B raw10379step0 raw10379step0Labels = mixedMoment B raw10379step1 raw10379step1Labels := by
      have ha : raw10379step1 = (fun i j => raw10379step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10379step1 raw10379step0; decide +kernel
      have hl : raw10379step1Labels = raw10379step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10379step0 raw10379step0Labels permutation40 permutation3
    _ = mixedMoment B node2998 node2998Labels := by rfl

def raw10380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10380 raw10380Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw10380 raw10380Labels = mixedMoment B raw10380step0 raw10380step0Labels := by
      have hz : ∀ j, raw10380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10380step0 = (fun i j => raw10380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10380step0 raw10380; decide +kernel
      have hl : raw10380step0Labels = raw10380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10380 raw10380Labels permutation346 hz
    mixedMoment B raw10380step0 raw10380step0Labels = mixedMoment B raw10380step1 raw10380step1Labels := by
      have ha : raw10380step1 = (fun i j => raw10380step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10380step1 raw10380step0; decide +kernel
      have hl : raw10380step1Labels = raw10380step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10380step0 raw10380step0Labels permutation46 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw10381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw10381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10381 raw10381Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw10381 raw10381Labels = mixedMoment B raw10381step0 raw10381step0Labels := by
      have hz : ∀ j, raw10381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10381step0 = (fun i j => raw10381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10381step0 raw10381; decide +kernel
      have hl : raw10381step0Labels = raw10381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10381 raw10381Labels permutation346 hz
    mixedMoment B raw10381step0 raw10381step0Labels = mixedMoment B raw10381step1 raw10381step1Labels := by
      have ha : raw10381step1 = (fun i j => raw10381step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10381step1 raw10381step0; decide +kernel
      have hl : raw10381step1Labels = raw10381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10381step0 raw10381step0Labels permutation41 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw10382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10382 raw10382Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw10382 raw10382Labels = mixedMoment B raw10382step0 raw10382step0Labels := by
      have hz : ∀ j, raw10382 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10382step0 = (fun i j => raw10382 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10382step0 raw10382; decide +kernel
      have hl : raw10382step0Labels = raw10382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10382 raw10382Labels permutation265 hz
    mixedMoment B raw10382step0 raw10382step0Labels = mixedMoment B raw10382step1 raw10382step1Labels := by
      have ha : raw10382step1 = (fun i j => raw10382step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10382step1 raw10382step0; decide +kernel
      have hl : raw10382step1Labels = raw10382step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10382step0 raw10382step0Labels permutation40 permutation3
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw10383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10383 raw10383Labels = mixedMoment B node2934 node2934Labels := by
  calc
    mixedMoment B raw10383 raw10383Labels = mixedMoment B raw10383step0 raw10383step0Labels := by
      have ha : raw10383step0 = (fun i j => raw10383 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10383step0 raw10383; decide +kernel
      have hl : raw10383step0Labels = raw10383Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10383 raw10383Labels permutation160 permutation3
    _ = mixedMoment B node2934 node2934Labels := by rfl

def raw10384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10384 raw10384Labels = mixedMoment B node2998 node2998Labels := by
  calc
    mixedMoment B raw10384 raw10384Labels = mixedMoment B raw10384step0 raw10384step0Labels := by
      have hz : ∀ j, raw10384 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10384step0 = (fun i j => raw10384 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10384step0 raw10384; decide +kernel
      have hl : raw10384step0Labels = raw10384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10384 raw10384Labels permutation265 hz
    mixedMoment B raw10384step0 raw10384step0Labels = mixedMoment B raw10384step1 raw10384step1Labels := by
      have ha : raw10384step1 = (fun i j => raw10384step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10384step1 raw10384step0; decide +kernel
      have hl : raw10384step1Labels = raw10384step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10384step0 raw10384step0Labels permutation40 permutation3
    _ = mixedMoment B node2998 node2998Labels := by rfl

def raw10385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10385 raw10385Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw10385 raw10385Labels = mixedMoment B raw10385step0 raw10385step0Labels := by
      have hz : ∀ j, raw10385 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10385step0 = (fun i j => raw10385 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10385step0 raw10385; decide +kernel
      have hl : raw10385step0Labels = raw10385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10385 raw10385Labels permutation265 hz
    mixedMoment B raw10385step0 raw10385step0Labels = mixedMoment B raw10385step1 raw10385step1Labels := by
      have ha : raw10385step1 = (fun i j => raw10385step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10385step1 raw10385step0; decide +kernel
      have hl : raw10385step1Labels = raw10385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10385step0 raw10385step0Labels permutation46 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw10386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw10386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10386 raw10386Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw10386 raw10386Labels = mixedMoment B raw10386step0 raw10386step0Labels := by
      have hz : ∀ j, raw10386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10386step0 = (fun i j => raw10386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10386step0 raw10386; decide +kernel
      have hl : raw10386step0Labels = raw10386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10386 raw10386Labels permutation265 hz
    mixedMoment B raw10386step0 raw10386step0Labels = mixedMoment B raw10386step1 raw10386step1Labels := by
      have ha : raw10386step1 = (fun i j => raw10386step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10386step1 raw10386step0; decide +kernel
      have hl : raw10386step1Labels = raw10386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10386step0 raw10386step0Labels permutation41 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw10387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10387step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10387 raw10387Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw10387 raw10387Labels = mixedMoment B raw10387step0 raw10387step0Labels := by
      have hz : ∀ j, raw10387 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10387step0 = (fun i j => raw10387 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10387step0 raw10387; decide +kernel
      have hl : raw10387step0Labels = raw10387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10387 raw10387Labels permutation346 hz
    mixedMoment B raw10387step0 raw10387step0Labels = mixedMoment B raw10387step1 raw10387step1Labels := by
      have hz : ∀ j, raw10387step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10387step1 = (fun i j => raw10387step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10387step1 raw10387step0; decide +kernel
      have hl : raw10387step1Labels = raw10387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10387step0 raw10387step0Labels permutation56 hz
    mixedMoment B raw10387step1 raw10387step1Labels = mixedMoment B raw10387step2 raw10387step2Labels := by
      have ha : raw10387step2 = (fun i j => raw10387step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10387step2 raw10387step1; decide +kernel
      have hl : raw10387step2Labels = raw10387step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10387step1 raw10387step1Labels permutation10 permutation3
    _ = mixedMoment B node1295 node1295Labels := by rfl

def raw10388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10388 raw10388Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw10388 raw10388Labels = mixedMoment B raw10388step0 raw10388step0Labels := by
      have hz : ∀ j, raw10388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10388step0 = (fun i j => raw10388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10388step0 raw10388; decide +kernel
      have hl : raw10388step0Labels = raw10388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10388 raw10388Labels permutation346 hz
    mixedMoment B raw10388step0 raw10388step0Labels = mixedMoment B raw10388step1 raw10388step1Labels := by
      have ha : raw10388step1 = (fun i j => raw10388step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10388step1 raw10388step0; decide +kernel
      have hl : raw10388step1Labels = raw10388step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10388step0 raw10388step0Labels permutation34 permutation3
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw10389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10389 raw10389Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw10389 raw10389Labels = mixedMoment B raw10389step0 raw10389step0Labels := by
      have hz : ∀ j, raw10389 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10389step0 = (fun i j => raw10389 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10389step0 raw10389; decide +kernel
      have hl : raw10389step0Labels = raw10389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10389 raw10389Labels permutation265 hz
    mixedMoment B raw10389step0 raw10389step0Labels = mixedMoment B raw10389step1 raw10389step1Labels := by
      have ha : raw10389step1 = (fun i j => raw10389step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10389step1 raw10389step0; decide +kernel
      have hl : raw10389step1Labels = raw10389step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10389step0 raw10389step0Labels permutation34 permutation3
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw10390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10390step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw10390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10390 raw10390Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw10390 raw10390Labels = mixedMoment B raw10390step0 raw10390step0Labels := by
      have hz : ∀ j, raw10390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10390step0 = (fun i j => raw10390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10390step0 raw10390; decide +kernel
      have hl : raw10390step0Labels = raw10390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10390 raw10390Labels permutation346 hz
    mixedMoment B raw10390step0 raw10390step0Labels = mixedMoment B raw10390step1 raw10390step1Labels := by
      have hz : ∀ j, raw10390step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10390step1 = (fun i j => raw10390step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10390step1 raw10390step0; decide +kernel
      have hl : raw10390step1Labels = raw10390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10390step0 raw10390step0Labels permutation56 hz
    mixedMoment B raw10390step1 raw10390step1Labels = mixedMoment B raw10390step2 raw10390step2Labels := by
      have ha : raw10390step2 = (fun i j => raw10390step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10390step2 raw10390step1; decide +kernel
      have hl : raw10390step2Labels = raw10390step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10390step1 raw10390step1Labels permutation10 permutation3
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw10391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10391step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10391 raw10391Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw10391 raw10391Labels = mixedMoment B raw10391step0 raw10391step0Labels := by
      have hz : ∀ j, raw10391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10391step0 = (fun i j => raw10391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10391step0 raw10391; decide +kernel
      have hl : raw10391step0Labels = raw10391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10391 raw10391Labels permutation346 hz
    mixedMoment B raw10391step0 raw10391step0Labels = mixedMoment B raw10391step1 raw10391step1Labels := by
      have hz : ∀ j, raw10391step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10391step1 = (fun i j => raw10391step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10391step1 raw10391step0; decide +kernel
      have hl : raw10391step1Labels = raw10391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10391step0 raw10391step0Labels permutation56 hz
    mixedMoment B raw10391step1 raw10391step1Labels = mixedMoment B raw10391step2 raw10391step2Labels := by
      have ha : raw10391step2 = (fun i j => raw10391step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10391step2 raw10391step1; decide +kernel
      have hl : raw10391step2Labels = raw10391step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10391step1 raw10391step1Labels permutation11 permutation3
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw10392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10392step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw10392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10392 raw10392Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw10392 raw10392Labels = mixedMoment B raw10392step0 raw10392step0Labels := by
      have hz : ∀ j, raw10392 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10392step0 = (fun i j => raw10392 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10392step0 raw10392; decide +kernel
      have hl : raw10392step0Labels = raw10392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10392 raw10392Labels permutation346 hz
    mixedMoment B raw10392step0 raw10392step0Labels = mixedMoment B raw10392step1 raw10392step1Labels := by
      have hz : ∀ j, raw10392step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10392step1 = (fun i j => raw10392step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10392step1 raw10392step0; decide +kernel
      have hl : raw10392step1Labels = raw10392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10392step0 raw10392step0Labels permutation56 hz
    mixedMoment B raw10392step1 raw10392step1Labels = mixedMoment B raw10392step2 raw10392step2Labels := by
      have ha : raw10392step2 = (fun i j => raw10392step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10392step2 raw10392step1; decide +kernel
      have hl : raw10392step2Labels = raw10392step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10392step1 raw10392step1Labels permutation8 permutation3
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw10393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw10393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10393 raw10393Labels = mixedMoment B node2943 node2943Labels := by
  calc
    mixedMoment B raw10393 raw10393Labels = mixedMoment B raw10393step0 raw10393step0Labels := by
      have hz : ∀ j, raw10393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10393step0 = (fun i j => raw10393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10393step0 raw10393; decide +kernel
      have hl : raw10393step0Labels = raw10393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10393 raw10393Labels permutation346 hz
    mixedMoment B raw10393step0 raw10393step0Labels = mixedMoment B raw10393step1 raw10393step1Labels := by
      have ha : raw10393step1 = (fun i j => raw10393step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10393step1 raw10393step0; decide +kernel
      have hl : raw10393step1Labels = raw10393step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10393step0 raw10393step0Labels permutation32 permutation3
    _ = mixedMoment B node2943 node2943Labels := by rfl

def raw10394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw10394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10394 raw10394Labels = mixedMoment B node2943 node2943Labels := by
  calc
    mixedMoment B raw10394 raw10394Labels = mixedMoment B raw10394step0 raw10394step0Labels := by
      have hz : ∀ j, raw10394 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10394step0 = (fun i j => raw10394 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10394step0 raw10394; decide +kernel
      have hl : raw10394step0Labels = raw10394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10394 raw10394Labels permutation265 hz
    mixedMoment B raw10394step0 raw10394step0Labels = mixedMoment B raw10394step1 raw10394step1Labels := by
      have ha : raw10394step1 = (fun i j => raw10394step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10394step1 raw10394step0; decide +kernel
      have hl : raw10394step1Labels = raw10394step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10394step0 raw10394step0Labels permutation32 permutation3
    _ = mixedMoment B node2943 node2943Labels := by rfl

def raw10395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10395step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10395 raw10395Labels = mixedMoment B node3006 node3006Labels := by
  calc
    mixedMoment B raw10395 raw10395Labels = mixedMoment B raw10395step0 raw10395step0Labels := by
      have hz : ∀ j, raw10395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10395step0 = (fun i j => raw10395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10395step0 raw10395; decide +kernel
      have hl : raw10395step0Labels = raw10395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10395 raw10395Labels permutation346 hz
    mixedMoment B raw10395step0 raw10395step0Labels = mixedMoment B raw10395step1 raw10395step1Labels := by
      have hz : ∀ j, raw10395step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10395step1 = (fun i j => raw10395step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10395step1 raw10395step0; decide +kernel
      have hl : raw10395step1Labels = raw10395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10395step0 raw10395step0Labels permutation56 hz
    mixedMoment B raw10395step1 raw10395step1Labels = mixedMoment B raw10395step2 raw10395step2Labels := by
      have ha : raw10395step2 = (fun i j => raw10395step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10395step2 raw10395step1; decide +kernel
      have hl : raw10395step2Labels = raw10395step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10395step1 raw10395step1Labels permutation8 permutation3
    _ = mixedMoment B node3006 node3006Labels := by rfl

def raw10396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10396step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10396 raw10396Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw10396 raw10396Labels = mixedMoment B raw10396step0 raw10396step0Labels := by
      have hz : ∀ j, raw10396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10396step0 = (fun i j => raw10396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10396step0 raw10396; decide +kernel
      have hl : raw10396step0Labels = raw10396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10396 raw10396Labels permutation346 hz
    mixedMoment B raw10396step0 raw10396step0Labels = mixedMoment B raw10396step1 raw10396step1Labels := by
      have hz : ∀ j, raw10396step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10396step1 = (fun i j => raw10396step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10396step1 raw10396step0; decide +kernel
      have hl : raw10396step1Labels = raw10396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10396step0 raw10396step0Labels permutation56 hz
    mixedMoment B raw10396step1 raw10396step1Labels = mixedMoment B raw10396step2 raw10396step2Labels := by
      have ha : raw10396step2 = (fun i j => raw10396step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10396step2 raw10396step1; decide +kernel
      have hl : raw10396step2Labels = raw10396step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10396step1 raw10396step1Labels permutation9 permutation3
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw10397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10397step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw10397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10397 raw10397Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw10397 raw10397Labels = mixedMoment B raw10397step0 raw10397step0Labels := by
      have hz : ∀ j, raw10397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10397step0 = (fun i j => raw10397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10397step0 raw10397; decide +kernel
      have hl : raw10397step0Labels = raw10397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10397 raw10397Labels permutation346 hz
    mixedMoment B raw10397step0 raw10397step0Labels = mixedMoment B raw10397step1 raw10397step1Labels := by
      have hz : ∀ j, raw10397step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10397step1 = (fun i j => raw10397step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10397step1 raw10397step0; decide +kernel
      have hl : raw10397step1Labels = raw10397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10397step0 raw10397step0Labels permutation56 hz
    mixedMoment B raw10397step1 raw10397step1Labels = mixedMoment B raw10397step2 raw10397step2Labels := by
      have ha : raw10397step2 = (fun i j => raw10397step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10397step2 raw10397step1; decide +kernel
      have hl : raw10397step2Labels = raw10397step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10397step1 raw10397step1Labels permutation8 permutation3
    _ = mixedMoment B node1264 node1264Labels := by rfl

def raw10398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw10398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10398step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw10398step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10398 raw10398Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw10398 raw10398Labels = mixedMoment B raw10398step0 raw10398step0Labels := by
      have hz : ∀ j, raw10398 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10398step0 = (fun i j => raw10398 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10398step0 raw10398; decide +kernel
      have hl : raw10398step0Labels = raw10398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10398 raw10398Labels permutation346 hz
    mixedMoment B raw10398step0 raw10398step0Labels = mixedMoment B raw10398step1 raw10398step1Labels := by
      have ha : raw10398step1 = (fun i j => raw10398step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10398step1 raw10398step0; decide +kernel
      have hl : raw10398step1Labels = raw10398step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10398step0 raw10398step0Labels permutation151 permutation3
    mixedMoment B raw10398step1 raw10398step1Labels = mixedMoment B raw10398step2 raw10398step2Labels := by
      have ha : raw10398step2 = -raw10398step1 := by apply Matrix.ext; change ∀ i j, raw10398step2 i j = -(raw10398step1 i j); unfold raw10398step2 raw10398step1; decide +kernel
      have hl : raw10398step2Labels = raw10398step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw10399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw10399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw10399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10399 raw10399Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw10399 raw10399Labels = mixedMoment B raw10399step0 raw10399step0Labels := by
      have hz : ∀ j, raw10399 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10399step0 = (fun i j => raw10399 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10399step0 raw10399; decide +kernel
      have hl : raw10399step0Labels = raw10399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10399 raw10399Labels permutation265 hz
    mixedMoment B raw10399step0 raw10399step0Labels = mixedMoment B raw10399step1 raw10399step1Labels := by
      have ha : raw10399step1 = (fun i j => raw10399step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10399step1 raw10399step0; decide +kernel
      have hl : raw10399step1Labels = raw10399step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10399step0 raw10399step0Labels permutation151 permutation3
    mixedMoment B raw10399step1 raw10399step1Labels = mixedMoment B raw10399step2 raw10399step2Labels := by
      have ha : raw10399step2 = -raw10399step1 := by apply Matrix.ext; change ∀ i j, raw10399step2 i j = -(raw10399step1 i j); unfold raw10399step2 raw10399step1; decide +kernel
      have hl : raw10399step2Labels = raw10399step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw10400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10400step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw10400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10400step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw10400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10400 raw10400Labels = mixedMoment B node2640 node2640Labels := by
  calc
    mixedMoment B raw10400 raw10400Labels = mixedMoment B raw10400step0 raw10400step0Labels := by
      have hz : ∀ j, raw10400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10400step0 = (fun i j => raw10400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10400step0 raw10400; decide +kernel
      have hl : raw10400step0Labels = raw10400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10400 raw10400Labels permutation346 hz
    mixedMoment B raw10400step0 raw10400step0Labels = mixedMoment B raw10400step1 raw10400step1Labels := by
      have hz : ∀ j, raw10400step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10400step1 = (fun i j => raw10400step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10400step1 raw10400step0; decide +kernel
      have hl : raw10400step1Labels = raw10400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10400step0 raw10400step0Labels permutation56 hz
    mixedMoment B raw10400step1 raw10400step1Labels = mixedMoment B raw10400step2 raw10400step2Labels := by
      have ha : raw10400step2 = (fun i j => raw10400step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10400step2 raw10400step1; decide +kernel
      have hl : raw10400step2Labels = raw10400step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10400step1 raw10400step1Labels permutation31 permutation3
    mixedMoment B raw10400step2 raw10400step2Labels = mixedMoment B raw10400step3 raw10400step3Labels := by
      have ha : raw10400step3 = -raw10400step2 := by apply Matrix.ext; change ∀ i j, raw10400step3 i j = -(raw10400step2 i j); unfold raw10400step3 raw10400step2; decide +kernel
      have hl : raw10400step3Labels = raw10400step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2640 node2640Labels := by rfl

def raw10401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10401step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw10401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10401step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10401 raw10401Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw10401 raw10401Labels = mixedMoment B raw10401step0 raw10401step0Labels := by
      have hz : ∀ j, raw10401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10401step0 = (fun i j => raw10401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10401step0 raw10401; decide +kernel
      have hl : raw10401step0Labels = raw10401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10401 raw10401Labels permutation346 hz
    mixedMoment B raw10401step0 raw10401step0Labels = mixedMoment B raw10401step1 raw10401step1Labels := by
      have hz : ∀ j, raw10401step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10401step1 = (fun i j => raw10401step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10401step1 raw10401step0; decide +kernel
      have hl : raw10401step1Labels = raw10401step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10401step0 raw10401step0Labels permutation56 hz
    mixedMoment B raw10401step1 raw10401step1Labels = mixedMoment B raw10401step2 raw10401step2Labels := by
      have ha : raw10401step2 = (fun i j => raw10401step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10401step2 raw10401step1; decide +kernel
      have hl : raw10401step2Labels = raw10401step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10401step1 raw10401step1Labels permutation29 permutation3
    mixedMoment B raw10401step2 raw10401step2Labels = mixedMoment B raw10401step3 raw10401step3Labels := by
      have ha : raw10401step3 = -raw10401step2 := by apply Matrix.ext; change ∀ i j, raw10401step3 i j = -(raw10401step2 i j); unfold raw10401step3 raw10401step2; decide +kernel
      have hl : raw10401step3Labels = raw10401step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw10402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10402step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10402step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10402step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10402step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10402 raw10402Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw10402 raw10402Labels = mixedMoment B raw10402step0 raw10402step0Labels := by
      have hz : ∀ j, raw10402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10402step0 = (fun i j => raw10402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10402step0 raw10402; decide +kernel
      have hl : raw10402step0Labels = raw10402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10402 raw10402Labels permutation346 hz
    mixedMoment B raw10402step0 raw10402step0Labels = mixedMoment B raw10402step1 raw10402step1Labels := by
      have ha : raw10402step1 = (fun i j => raw10402step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10402step1 raw10402step0; decide +kernel
      have hl : raw10402step1Labels = raw10402step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10402step0 raw10402step0Labels permutation39 permutation7
    mixedMoment B raw10402step1 raw10402step1Labels = mixedMoment B raw10402step2 raw10402step2Labels := by
      have ha : raw10402step2 = -raw10402step1 := by apply Matrix.ext; change ∀ i j, raw10402step2 i j = -(raw10402step1 i j); unfold raw10402step2 raw10402step1; decide +kernel
      have hl : raw10402step2Labels = raw10402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10402step2 raw10402step2Labels = mixedMoment B raw10402step3 raw10402step3Labels := by
      have ha : raw10402step3 = raw10402step2 := by apply Matrix.ext; unfold raw10402step3 raw10402step2; decide +kernel
      have hl : raw10402step2Labels = labelEmbedding1 ∘ raw10402step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10402step2 raw10402step2Labels raw10402step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw10403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10403step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10403step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10403step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10403 raw10403Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw10403 raw10403Labels = mixedMoment B raw10403step0 raw10403step0Labels := by
      have hz : ∀ j, raw10403 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10403step0 = (fun i j => raw10403 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10403step0 raw10403; decide +kernel
      have hl : raw10403step0Labels = raw10403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10403 raw10403Labels permutation265 hz
    mixedMoment B raw10403step0 raw10403step0Labels = mixedMoment B raw10403step1 raw10403step1Labels := by
      have ha : raw10403step1 = (fun i j => raw10403step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10403step1 raw10403step0; decide +kernel
      have hl : raw10403step1Labels = raw10403step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10403step0 raw10403step0Labels permutation39 permutation7
    mixedMoment B raw10403step1 raw10403step1Labels = mixedMoment B raw10403step2 raw10403step2Labels := by
      have ha : raw10403step2 = -raw10403step1 := by apply Matrix.ext; change ∀ i j, raw10403step2 i j = -(raw10403step1 i j); unfold raw10403step2 raw10403step1; decide +kernel
      have hl : raw10403step2Labels = raw10403step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10403step2 raw10403step2Labels = mixedMoment B raw10403step3 raw10403step3Labels := by
      have ha : raw10403step3 = raw10403step2 := by apply Matrix.ext; unfold raw10403step3 raw10403step2; decide +kernel
      have hl : raw10403step2Labels = labelEmbedding1 ∘ raw10403step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10403step2 raw10403step2Labels raw10403step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw10404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10404step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10404step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10404step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10404step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10404 raw10404Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw10404 raw10404Labels = mixedMoment B raw10404step0 raw10404step0Labels := by
      have hz : ∀ j, raw10404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10404step0 = (fun i j => raw10404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10404step0 raw10404; decide +kernel
      have hl : raw10404step0Labels = raw10404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10404 raw10404Labels permutation346 hz
    mixedMoment B raw10404step0 raw10404step0Labels = mixedMoment B raw10404step1 raw10404step1Labels := by
      have hz : ∀ j, raw10404step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10404step1 = (fun i j => raw10404step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10404step1 raw10404step0; decide +kernel
      have hl : raw10404step1Labels = raw10404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10404step0 raw10404step0Labels permutation56 hz
    mixedMoment B raw10404step1 raw10404step1Labels = mixedMoment B raw10404step2 raw10404step2Labels := by
      have ha : raw10404step2 = (fun i j => raw10404step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10404step2 raw10404step1; decide +kernel
      have hl : raw10404step2Labels = raw10404step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10404step1 raw10404step1Labels permutation9 permutation7
    mixedMoment B raw10404step2 raw10404step2Labels = mixedMoment B raw10404step3 raw10404step3Labels := by
      have ha : raw10404step3 = -raw10404step2 := by apply Matrix.ext; change ∀ i j, raw10404step3 i j = -(raw10404step2 i j); unfold raw10404step3 raw10404step2; decide +kernel
      have hl : raw10404step3Labels = raw10404step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10404step3 raw10404step3Labels = mixedMoment B raw10404step4 raw10404step4Labels := by
      have ha : raw10404step4 = raw10404step3 := by apply Matrix.ext; unfold raw10404step4 raw10404step3; decide +kernel
      have hl : raw10404step3Labels = labelEmbedding1 ∘ raw10404step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10404step3 raw10404step3Labels raw10404step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw10405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10405step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10405step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10405step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10405step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10405step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10405step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10405step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10405 raw10405Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw10405 raw10405Labels = mixedMoment B raw10405step0 raw10405step0Labels := by
      have hz : ∀ j, raw10405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10405step0 = (fun i j => raw10405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10405step0 raw10405; decide +kernel
      have hl : raw10405step0Labels = raw10405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10405 raw10405Labels permutation346 hz
    mixedMoment B raw10405step0 raw10405step0Labels = mixedMoment B raw10405step1 raw10405step1Labels := by
      have hz : ∀ j, raw10405step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10405step1 = (fun i j => raw10405step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10405step1 raw10405step0; decide +kernel
      have hl : raw10405step1Labels = raw10405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10405step0 raw10405step0Labels permutation56 hz
    mixedMoment B raw10405step1 raw10405step1Labels = mixedMoment B raw10405step2 raw10405step2Labels := by
      have ha : raw10405step2 = (fun i j => raw10405step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10405step2 raw10405step1; decide +kernel
      have hl : raw10405step2Labels = raw10405step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10405step1 raw10405step1Labels permutation9 permutation7
    mixedMoment B raw10405step2 raw10405step2Labels = mixedMoment B raw10405step3 raw10405step3Labels := by
      have ha : raw10405step3 = -raw10405step2 := by apply Matrix.ext; change ∀ i j, raw10405step3 i j = -(raw10405step2 i j); unfold raw10405step3 raw10405step2; decide +kernel
      have hl : raw10405step3Labels = raw10405step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10405step3 raw10405step3Labels = mixedMoment B raw10405step4 raw10405step4Labels := by
      have ha : raw10405step4 = raw10405step3 := by apply Matrix.ext; unfold raw10405step4 raw10405step3; decide +kernel
      have hl : raw10405step3Labels = labelEmbedding1 ∘ raw10405step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10405step3 raw10405step3Labels raw10405step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw10406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10406step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw10406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10406step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10406step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10406step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10406 raw10406Labels = mixedMoment B node3861 node3861Labels := by
  calc
    mixedMoment B raw10406 raw10406Labels = mixedMoment B raw10406step0 raw10406step0Labels := by
      have hz : ∀ j, raw10406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10406step0 = (fun i j => raw10406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10406step0 raw10406; decide +kernel
      have hl : raw10406step0Labels = raw10406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10406 raw10406Labels permutation346 hz
    mixedMoment B raw10406step0 raw10406step0Labels = mixedMoment B raw10406step1 raw10406step1Labels := by
      have hz : ∀ j, raw10406step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10406step1 = (fun i j => raw10406step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10406step1 raw10406step0; decide +kernel
      have hl : raw10406step1Labels = raw10406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10406step0 raw10406step0Labels permutation56 hz
    mixedMoment B raw10406step1 raw10406step1Labels = mixedMoment B raw10406step2 raw10406step2Labels := by
      have ha : raw10406step2 = (fun i j => raw10406step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10406step2 raw10406step1; decide +kernel
      have hl : raw10406step2Labels = raw10406step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10406step1 raw10406step1Labels permutation9 permutation7
    mixedMoment B raw10406step2 raw10406step2Labels = mixedMoment B raw10406step3 raw10406step3Labels := by
      have ha : raw10406step3 = -raw10406step2 := by apply Matrix.ext; change ∀ i j, raw10406step3 i j = -(raw10406step2 i j); unfold raw10406step3 raw10406step2; decide +kernel
      have hl : raw10406step3Labels = raw10406step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10406step3 raw10406step3Labels = mixedMoment B raw10406step4 raw10406step4Labels := by
      have ha : raw10406step4 = raw10406step3 := by apply Matrix.ext; unfold raw10406step4 raw10406step3; decide +kernel
      have hl : raw10406step3Labels = labelEmbedding1 ∘ raw10406step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10406step3 raw10406step3Labels raw10406step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3861 node3861Labels := by rfl

def raw10407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10407step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10407step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10407step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10407 raw10407Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw10407 raw10407Labels = mixedMoment B raw10407step0 raw10407step0Labels := by
      have hz : ∀ j, raw10407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10407step0 = (fun i j => raw10407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10407step0 raw10407; decide +kernel
      have hl : raw10407step0Labels = raw10407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10407 raw10407Labels permutation346 hz
    mixedMoment B raw10407step0 raw10407step0Labels = mixedMoment B raw10407step1 raw10407step1Labels := by
      have ha : raw10407step1 = (fun i j => raw10407step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10407step1 raw10407step0; decide +kernel
      have hl : raw10407step1Labels = raw10407step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10407step0 raw10407step0Labels permutation39 permutation7
    mixedMoment B raw10407step1 raw10407step1Labels = mixedMoment B raw10407step2 raw10407step2Labels := by
      have ha : raw10407step2 = -raw10407step1 := by apply Matrix.ext; change ∀ i j, raw10407step2 i j = -(raw10407step1 i j); unfold raw10407step2 raw10407step1; decide +kernel
      have hl : raw10407step2Labels = raw10407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10407step2 raw10407step2Labels = mixedMoment B raw10407step3 raw10407step3Labels := by
      have ha : raw10407step3 = raw10407step2 := by apply Matrix.ext; unfold raw10407step3 raw10407step2; decide +kernel
      have hl : raw10407step2Labels = labelEmbedding1 ∘ raw10407step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10407step2 raw10407step2Labels raw10407step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw10408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10408 raw10408Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw10408 raw10408Labels = mixedMoment B raw10408step0 raw10408step0Labels := by
      have ha : raw10408step0 = (fun i j => raw10408 (permutation207 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10408step0 raw10408; decide +kernel
      have hl : raw10408step0Labels = raw10408Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10408 raw10408Labels permutation207 permutation7
    mixedMoment B raw10408step0 raw10408step0Labels = mixedMoment B raw10408step1 raw10408step1Labels := by
      have ha : raw10408step1 = -raw10408step0 := by apply Matrix.ext; change ∀ i j, raw10408step1 i j = -(raw10408step0 i j); unfold raw10408step1 raw10408step0; decide +kernel
      have hl : raw10408step1Labels = raw10408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10408step1 raw10408step1Labels = mixedMoment B raw10408step2 raw10408step2Labels := by
      have ha : raw10408step2 = raw10408step1 := by apply Matrix.ext; unfold raw10408step2 raw10408step1; decide +kernel
      have hl : raw10408step1Labels = labelEmbedding1 ∘ raw10408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10408step1 raw10408step1Labels raw10408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3515 node3515Labels := by rfl

def raw10409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10409step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10409step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10409step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10409 raw10409Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw10409 raw10409Labels = mixedMoment B raw10409step0 raw10409step0Labels := by
      have hz : ∀ j, raw10409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10409step0 = (fun i j => raw10409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10409step0 raw10409; decide +kernel
      have hl : raw10409step0Labels = raw10409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10409 raw10409Labels permutation346 hz
    mixedMoment B raw10409step0 raw10409step0Labels = mixedMoment B raw10409step1 raw10409step1Labels := by
      have ha : raw10409step1 = (fun i j => raw10409step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10409step1 raw10409step0; decide +kernel
      have hl : raw10409step1Labels = raw10409step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10409step0 raw10409step0Labels permutation39 permutation7
    mixedMoment B raw10409step1 raw10409step1Labels = mixedMoment B raw10409step2 raw10409step2Labels := by
      have ha : raw10409step2 = -raw10409step1 := by apply Matrix.ext; change ∀ i j, raw10409step2 i j = -(raw10409step1 i j); unfold raw10409step2 raw10409step1; decide +kernel
      have hl : raw10409step2Labels = raw10409step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10409step2 raw10409step2Labels = mixedMoment B raw10409step3 raw10409step3Labels := by
      have ha : raw10409step3 = raw10409step2 := by apply Matrix.ext; unfold raw10409step3 raw10409step2; decide +kernel
      have hl : raw10409step2Labels = labelEmbedding1 ∘ raw10409step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10409step2 raw10409step2Labels raw10409step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw10410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10410step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10410step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10410step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10410step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10410 raw10410Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw10410 raw10410Labels = mixedMoment B raw10410step0 raw10410step0Labels := by
      have hz : ∀ j, raw10410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10410step0 = (fun i j => raw10410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10410step0 raw10410; decide +kernel
      have hl : raw10410step0Labels = raw10410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10410 raw10410Labels permutation346 hz
    mixedMoment B raw10410step0 raw10410step0Labels = mixedMoment B raw10410step1 raw10410step1Labels := by
      have ha : raw10410step1 = (fun i j => raw10410step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10410step1 raw10410step0; decide +kernel
      have hl : raw10410step1Labels = raw10410step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10410step0 raw10410step0Labels permutation39 permutation7
    mixedMoment B raw10410step1 raw10410step1Labels = mixedMoment B raw10410step2 raw10410step2Labels := by
      have ha : raw10410step2 = -raw10410step1 := by apply Matrix.ext; change ∀ i j, raw10410step2 i j = -(raw10410step1 i j); unfold raw10410step2 raw10410step1; decide +kernel
      have hl : raw10410step2Labels = raw10410step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10410step2 raw10410step2Labels = mixedMoment B raw10410step3 raw10410step3Labels := by
      have ha : raw10410step3 = raw10410step2 := by apply Matrix.ext; unfold raw10410step3 raw10410step2; decide +kernel
      have hl : raw10410step2Labels = labelEmbedding1 ∘ raw10410step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10410step2 raw10410step2Labels raw10410step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw10411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10411step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10411step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10411step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10411 raw10411Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw10411 raw10411Labels = mixedMoment B raw10411step0 raw10411step0Labels := by
      have hz : ∀ j, raw10411 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10411step0 = (fun i j => raw10411 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10411step0 raw10411; decide +kernel
      have hl : raw10411step0Labels = raw10411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10411 raw10411Labels permutation346 hz
    mixedMoment B raw10411step0 raw10411step0Labels = mixedMoment B raw10411step1 raw10411step1Labels := by
      have ha : raw10411step1 = (fun i j => raw10411step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10411step1 raw10411step0; decide +kernel
      have hl : raw10411step1Labels = raw10411step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10411step0 raw10411step0Labels permutation39 permutation7
    mixedMoment B raw10411step1 raw10411step1Labels = mixedMoment B raw10411step2 raw10411step2Labels := by
      have ha : raw10411step2 = -raw10411step1 := by apply Matrix.ext; change ∀ i j, raw10411step2 i j = -(raw10411step1 i j); unfold raw10411step2 raw10411step1; decide +kernel
      have hl : raw10411step2Labels = raw10411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10411step2 raw10411step2Labels = mixedMoment B raw10411step3 raw10411step3Labels := by
      have ha : raw10411step3 = raw10411step2 := by apply Matrix.ext; unfold raw10411step3 raw10411step2; decide +kernel
      have hl : raw10411step2Labels = labelEmbedding1 ∘ raw10411step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10411step2 raw10411step2Labels raw10411step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw10412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10412step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10412step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10412step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10412 raw10412Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw10412 raw10412Labels = mixedMoment B raw10412step0 raw10412step0Labels := by
      have hz : ∀ j, raw10412 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10412step0 = (fun i j => raw10412 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10412step0 raw10412; decide +kernel
      have hl : raw10412step0Labels = raw10412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10412 raw10412Labels permutation265 hz
    mixedMoment B raw10412step0 raw10412step0Labels = mixedMoment B raw10412step1 raw10412step1Labels := by
      have ha : raw10412step1 = (fun i j => raw10412step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10412step1 raw10412step0; decide +kernel
      have hl : raw10412step1Labels = raw10412step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10412step0 raw10412step0Labels permutation39 permutation7
    mixedMoment B raw10412step1 raw10412step1Labels = mixedMoment B raw10412step2 raw10412step2Labels := by
      have ha : raw10412step2 = -raw10412step1 := by apply Matrix.ext; change ∀ i j, raw10412step2 i j = -(raw10412step1 i j); unfold raw10412step2 raw10412step1; decide +kernel
      have hl : raw10412step2Labels = raw10412step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10412step2 raw10412step2Labels = mixedMoment B raw10412step3 raw10412step3Labels := by
      have ha : raw10412step3 = raw10412step2 := by apply Matrix.ext; unfold raw10412step3 raw10412step2; decide +kernel
      have hl : raw10412step2Labels = labelEmbedding1 ∘ raw10412step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10412step2 raw10412step2Labels raw10412step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw10413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10413step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10413step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10413 raw10413Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw10413 raw10413Labels = mixedMoment B raw10413step0 raw10413step0Labels := by
      have ha : raw10413step0 = (fun i j => raw10413 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10413step0 raw10413; decide +kernel
      have hl : raw10413step0Labels = raw10413Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10413 raw10413Labels permutation201 permutation7
    mixedMoment B raw10413step0 raw10413step0Labels = mixedMoment B raw10413step1 raw10413step1Labels := by
      have ha : raw10413step1 = -raw10413step0 := by apply Matrix.ext; change ∀ i j, raw10413step1 i j = -(raw10413step0 i j); unfold raw10413step1 raw10413step0; decide +kernel
      have hl : raw10413step1Labels = raw10413step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10413step1 raw10413step1Labels = mixedMoment B raw10413step2 raw10413step2Labels := by
      have ha : raw10413step2 = raw10413step1 := by apply Matrix.ext; unfold raw10413step2 raw10413step1; decide +kernel
      have hl : raw10413step1Labels = labelEmbedding1 ∘ raw10413step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10413step1 raw10413step1Labels raw10413step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3515 node3515Labels := by rfl

def raw10414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10414step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10414step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10414step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10414step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10414step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10414 raw10414Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw10414 raw10414Labels = mixedMoment B raw10414step0 raw10414step0Labels := by
      have hz : ∀ j, raw10414 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10414step0 = (fun i j => raw10414 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10414step0 raw10414; decide +kernel
      have hl : raw10414step0Labels = raw10414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10414 raw10414Labels permutation265 hz
    mixedMoment B raw10414step0 raw10414step0Labels = mixedMoment B raw10414step1 raw10414step1Labels := by
      have ha : raw10414step1 = (fun i j => raw10414step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10414step1 raw10414step0; decide +kernel
      have hl : raw10414step1Labels = raw10414step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10414step0 raw10414step0Labels permutation39 permutation7
    mixedMoment B raw10414step1 raw10414step1Labels = mixedMoment B raw10414step2 raw10414step2Labels := by
      have ha : raw10414step2 = -raw10414step1 := by apply Matrix.ext; change ∀ i j, raw10414step2 i j = -(raw10414step1 i j); unfold raw10414step2 raw10414step1; decide +kernel
      have hl : raw10414step2Labels = raw10414step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10414step2 raw10414step2Labels = mixedMoment B raw10414step3 raw10414step3Labels := by
      have ha : raw10414step3 = raw10414step2 := by apply Matrix.ext; unfold raw10414step3 raw10414step2; decide +kernel
      have hl : raw10414step2Labels = labelEmbedding1 ∘ raw10414step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10414step2 raw10414step2Labels raw10414step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw10415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10415step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10415step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10415 raw10415Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw10415 raw10415Labels = mixedMoment B raw10415step0 raw10415step0Labels := by
      have hz : ∀ j, raw10415 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10415step0 = (fun i j => raw10415 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10415step0 raw10415; decide +kernel
      have hl : raw10415step0Labels = raw10415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10415 raw10415Labels permutation265 hz
    mixedMoment B raw10415step0 raw10415step0Labels = mixedMoment B raw10415step1 raw10415step1Labels := by
      have ha : raw10415step1 = (fun i j => raw10415step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10415step1 raw10415step0; decide +kernel
      have hl : raw10415step1Labels = raw10415step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10415step0 raw10415step0Labels permutation39 permutation7
    mixedMoment B raw10415step1 raw10415step1Labels = mixedMoment B raw10415step2 raw10415step2Labels := by
      have ha : raw10415step2 = -raw10415step1 := by apply Matrix.ext; change ∀ i j, raw10415step2 i j = -(raw10415step1 i j); unfold raw10415step2 raw10415step1; decide +kernel
      have hl : raw10415step2Labels = raw10415step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10415step2 raw10415step2Labels = mixedMoment B raw10415step3 raw10415step3Labels := by
      have ha : raw10415step3 = raw10415step2 := by apply Matrix.ext; unfold raw10415step3 raw10415step2; decide +kernel
      have hl : raw10415step2Labels = labelEmbedding1 ∘ raw10415step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10415step2 raw10415step2Labels raw10415step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw10416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10416step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10416step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10416step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10416 raw10416Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw10416 raw10416Labels = mixedMoment B raw10416step0 raw10416step0Labels := by
      have hz : ∀ j, raw10416 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10416step0 = (fun i j => raw10416 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10416step0 raw10416; decide +kernel
      have hl : raw10416step0Labels = raw10416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10416 raw10416Labels permutation265 hz
    mixedMoment B raw10416step0 raw10416step0Labels = mixedMoment B raw10416step1 raw10416step1Labels := by
      have ha : raw10416step1 = (fun i j => raw10416step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10416step1 raw10416step0; decide +kernel
      have hl : raw10416step1Labels = raw10416step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10416step0 raw10416step0Labels permutation39 permutation7
    mixedMoment B raw10416step1 raw10416step1Labels = mixedMoment B raw10416step2 raw10416step2Labels := by
      have ha : raw10416step2 = -raw10416step1 := by apply Matrix.ext; change ∀ i j, raw10416step2 i j = -(raw10416step1 i j); unfold raw10416step2 raw10416step1; decide +kernel
      have hl : raw10416step2Labels = raw10416step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10416step2 raw10416step2Labels = mixedMoment B raw10416step3 raw10416step3Labels := by
      have ha : raw10416step3 = raw10416step2 := by apply Matrix.ext; unfold raw10416step3 raw10416step2; decide +kernel
      have hl : raw10416step2Labels = labelEmbedding1 ∘ raw10416step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10416step2 raw10416step2Labels raw10416step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw10417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10417step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10417step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10417step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10417step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10417step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10417 raw10417Labels = mixedMoment B node3306 node3306Labels := by
  calc
    mixedMoment B raw10417 raw10417Labels = mixedMoment B raw10417step0 raw10417step0Labels := by
      have hz : ∀ j, raw10417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10417step0 = (fun i j => raw10417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10417step0 raw10417; decide +kernel
      have hl : raw10417step0Labels = raw10417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10417 raw10417Labels permutation346 hz
    mixedMoment B raw10417step0 raw10417step0Labels = mixedMoment B raw10417step1 raw10417step1Labels := by
      have hz : ∀ j, raw10417step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10417step1 = (fun i j => raw10417step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10417step1 raw10417step0; decide +kernel
      have hl : raw10417step1Labels = raw10417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10417step0 raw10417step0Labels permutation56 hz
    mixedMoment B raw10417step1 raw10417step1Labels = mixedMoment B raw10417step2 raw10417step2Labels := by
      have ha : raw10417step2 = (fun i j => raw10417step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10417step2 raw10417step1; decide +kernel
      have hl : raw10417step2Labels = raw10417step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10417step1 raw10417step1Labels permutation11 permutation5
    mixedMoment B raw10417step2 raw10417step2Labels = mixedMoment B raw10417step3 raw10417step3Labels := by
      have ha : raw10417step3 = -raw10417step2 := by apply Matrix.ext; change ∀ i j, raw10417step3 i j = -(raw10417step2 i j); unfold raw10417step3 raw10417step2; decide +kernel
      have hl : raw10417step3Labels = raw10417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10417step3 raw10417step3Labels = mixedMoment B raw10417step4 raw10417step4Labels := by
      have ha : raw10417step4 = raw10417step3 := by apply Matrix.ext; unfold raw10417step4 raw10417step3; decide +kernel
      have hl : raw10417step3Labels = labelEmbedding1 ∘ raw10417step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10417step3 raw10417step3Labels raw10417step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3306 node3306Labels := by rfl

def raw10418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10418step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10418step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10418step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10418step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10418 raw10418Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw10418 raw10418Labels = mixedMoment B raw10418step0 raw10418step0Labels := by
      have hz : ∀ j, raw10418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10418step0 = (fun i j => raw10418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10418step0 raw10418; decide +kernel
      have hl : raw10418step0Labels = raw10418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10418 raw10418Labels permutation346 hz
    mixedMoment B raw10418step0 raw10418step0Labels = mixedMoment B raw10418step1 raw10418step1Labels := by
      have ha : raw10418step1 = (fun i j => raw10418step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10418step1 raw10418step0; decide +kernel
      have hl : raw10418step1Labels = raw10418step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10418step0 raw10418step0Labels permutation39 permutation7
    mixedMoment B raw10418step1 raw10418step1Labels = mixedMoment B raw10418step2 raw10418step2Labels := by
      have ha : raw10418step2 = -raw10418step1 := by apply Matrix.ext; change ∀ i j, raw10418step2 i j = -(raw10418step1 i j); unfold raw10418step2 raw10418step1; decide +kernel
      have hl : raw10418step2Labels = raw10418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10418step2 raw10418step2Labels = mixedMoment B raw10418step3 raw10418step3Labels := by
      have ha : raw10418step3 = raw10418step2 := by apply Matrix.ext; unfold raw10418step3 raw10418step2; decide +kernel
      have hl : raw10418step2Labels = labelEmbedding1 ∘ raw10418step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10418step2 raw10418step2Labels raw10418step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw10419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10419Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10419step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10419step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10419step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10419step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10419step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10419step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10419 raw10419Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw10419 raw10419Labels = mixedMoment B raw10419step0 raw10419step0Labels := by
      have hz : ∀ j, raw10419 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10419step0 = (fun i j => raw10419 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10419step0 raw10419; decide +kernel
      have hl : raw10419step0Labels = raw10419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10419 raw10419Labels permutation265 hz
    mixedMoment B raw10419step0 raw10419step0Labels = mixedMoment B raw10419step1 raw10419step1Labels := by
      have ha : raw10419step1 = (fun i j => raw10419step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10419step1 raw10419step0; decide +kernel
      have hl : raw10419step1Labels = raw10419step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10419step0 raw10419step0Labels permutation39 permutation7
    mixedMoment B raw10419step1 raw10419step1Labels = mixedMoment B raw10419step2 raw10419step2Labels := by
      have ha : raw10419step2 = -raw10419step1 := by apply Matrix.ext; change ∀ i j, raw10419step2 i j = -(raw10419step1 i j); unfold raw10419step2 raw10419step1; decide +kernel
      have hl : raw10419step2Labels = raw10419step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10419step2 raw10419step2Labels = mixedMoment B raw10419step3 raw10419step3Labels := by
      have ha : raw10419step3 = raw10419step2 := by apply Matrix.ext; unfold raw10419step3 raw10419step2; decide +kernel
      have hl : raw10419step2Labels = labelEmbedding1 ∘ raw10419step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10419step2 raw10419step2Labels raw10419step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw10420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10420step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10420step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10420step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10420step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10420step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10420step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10420step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10420 raw10420Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw10420 raw10420Labels = mixedMoment B raw10420step0 raw10420step0Labels := by
      have hz : ∀ j, raw10420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10420step0 = (fun i j => raw10420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10420step0 raw10420; decide +kernel
      have hl : raw10420step0Labels = raw10420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10420 raw10420Labels permutation346 hz
    mixedMoment B raw10420step0 raw10420step0Labels = mixedMoment B raw10420step1 raw10420step1Labels := by
      have hz : ∀ j, raw10420step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10420step1 = (fun i j => raw10420step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10420step1 raw10420step0; decide +kernel
      have hl : raw10420step1Labels = raw10420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10420step0 raw10420step0Labels permutation56 hz
    mixedMoment B raw10420step1 raw10420step1Labels = mixedMoment B raw10420step2 raw10420step2Labels := by
      have ha : raw10420step2 = (fun i j => raw10420step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10420step2 raw10420step1; decide +kernel
      have hl : raw10420step2Labels = raw10420step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10420step1 raw10420step1Labels permutation9 permutation7
    mixedMoment B raw10420step2 raw10420step2Labels = mixedMoment B raw10420step3 raw10420step3Labels := by
      have ha : raw10420step3 = -raw10420step2 := by apply Matrix.ext; change ∀ i j, raw10420step3 i j = -(raw10420step2 i j); unfold raw10420step3 raw10420step2; decide +kernel
      have hl : raw10420step3Labels = raw10420step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10420step3 raw10420step3Labels = mixedMoment B raw10420step4 raw10420step4Labels := by
      have ha : raw10420step4 = raw10420step3 := by apply Matrix.ext; unfold raw10420step4 raw10420step3; decide +kernel
      have hl : raw10420step3Labels = labelEmbedding1 ∘ raw10420step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10420step3 raw10420step3Labels raw10420step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw10421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10421step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10421step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10421step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10421step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10421step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10421step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10421 raw10421Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw10421 raw10421Labels = mixedMoment B raw10421step0 raw10421step0Labels := by
      have hz : ∀ j, raw10421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10421step0 = (fun i j => raw10421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10421step0 raw10421; decide +kernel
      have hl : raw10421step0Labels = raw10421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10421 raw10421Labels permutation346 hz
    mixedMoment B raw10421step0 raw10421step0Labels = mixedMoment B raw10421step1 raw10421step1Labels := by
      have hz : ∀ j, raw10421step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10421step1 = (fun i j => raw10421step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10421step1 raw10421step0; decide +kernel
      have hl : raw10421step1Labels = raw10421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10421step0 raw10421step0Labels permutation56 hz
    mixedMoment B raw10421step1 raw10421step1Labels = mixedMoment B raw10421step2 raw10421step2Labels := by
      have ha : raw10421step2 = (fun i j => raw10421step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10421step2 raw10421step1; decide +kernel
      have hl : raw10421step2Labels = raw10421step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10421step1 raw10421step1Labels permutation9 permutation7
    mixedMoment B raw10421step2 raw10421step2Labels = mixedMoment B raw10421step3 raw10421step3Labels := by
      have ha : raw10421step3 = -raw10421step2 := by apply Matrix.ext; change ∀ i j, raw10421step3 i j = -(raw10421step2 i j); unfold raw10421step3 raw10421step2; decide +kernel
      have hl : raw10421step3Labels = raw10421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10421step3 raw10421step3Labels = mixedMoment B raw10421step4 raw10421step4Labels := by
      have ha : raw10421step4 = raw10421step3 := by apply Matrix.ext; unfold raw10421step4 raw10421step3; decide +kernel
      have hl : raw10421step3Labels = labelEmbedding1 ∘ raw10421step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10421step3 raw10421step3Labels raw10421step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw10422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10422step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10422step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw10422step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10422step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10422step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10422step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10422step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10422 raw10422Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw10422 raw10422Labels = mixedMoment B raw10422step0 raw10422step0Labels := by
      have hz : ∀ j, raw10422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10422step0 = (fun i j => raw10422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10422step0 raw10422; decide +kernel
      have hl : raw10422step0Labels = raw10422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10422 raw10422Labels permutation346 hz
    mixedMoment B raw10422step0 raw10422step0Labels = mixedMoment B raw10422step1 raw10422step1Labels := by
      have hz : ∀ j, raw10422step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10422step1 = (fun i j => raw10422step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10422step1 raw10422step0; decide +kernel
      have hl : raw10422step1Labels = raw10422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10422step0 raw10422step0Labels permutation56 hz
    mixedMoment B raw10422step1 raw10422step1Labels = mixedMoment B raw10422step2 raw10422step2Labels := by
      have ha : raw10422step2 = (fun i j => raw10422step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10422step2 raw10422step1; decide +kernel
      have hl : raw10422step2Labels = raw10422step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10422step1 raw10422step1Labels permutation9 permutation7
    mixedMoment B raw10422step2 raw10422step2Labels = mixedMoment B raw10422step3 raw10422step3Labels := by
      have ha : raw10422step3 = -raw10422step2 := by apply Matrix.ext; change ∀ i j, raw10422step3 i j = -(raw10422step2 i j); unfold raw10422step3 raw10422step2; decide +kernel
      have hl : raw10422step3Labels = raw10422step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10422step3 raw10422step3Labels = mixedMoment B raw10422step4 raw10422step4Labels := by
      have ha : raw10422step4 = raw10422step3 := by apply Matrix.ext; unfold raw10422step4 raw10422step3; decide +kernel
      have hl : raw10422step3Labels = labelEmbedding1 ∘ raw10422step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10422step3 raw10422step3Labels raw10422step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw10423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10423step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw10423step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10423step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10423step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10423step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10423 raw10423Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw10423 raw10423Labels = mixedMoment B raw10423step0 raw10423step0Labels := by
      have hz : ∀ j, raw10423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10423step0 = (fun i j => raw10423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10423step0 raw10423; decide +kernel
      have hl : raw10423step0Labels = raw10423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10423 raw10423Labels permutation346 hz
    mixedMoment B raw10423step0 raw10423step0Labels = mixedMoment B raw10423step1 raw10423step1Labels := by
      have ha : raw10423step1 = (fun i j => raw10423step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10423step1 raw10423step0; decide +kernel
      have hl : raw10423step1Labels = raw10423step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10423step0 raw10423step0Labels permutation39 permutation7
    mixedMoment B raw10423step1 raw10423step1Labels = mixedMoment B raw10423step2 raw10423step2Labels := by
      have ha : raw10423step2 = -raw10423step1 := by apply Matrix.ext; change ∀ i j, raw10423step2 i j = -(raw10423step1 i j); unfold raw10423step2 raw10423step1; decide +kernel
      have hl : raw10423step2Labels = raw10423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10423step2 raw10423step2Labels = mixedMoment B raw10423step3 raw10423step3Labels := by
      have ha : raw10423step3 = raw10423step2 := by apply Matrix.ext; unfold raw10423step3 raw10423step2; decide +kernel
      have hl : raw10423step2Labels = labelEmbedding1 ∘ raw10423step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10423step2 raw10423step2Labels raw10423step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw10424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10424step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw10424step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10424step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10424step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10424 raw10424Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw10424 raw10424Labels = mixedMoment B raw10424step0 raw10424step0Labels := by
      have hz : ∀ j, raw10424 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10424step0 = (fun i j => raw10424 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10424step0 raw10424; decide +kernel
      have hl : raw10424step0Labels = raw10424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10424 raw10424Labels permutation265 hz
    mixedMoment B raw10424step0 raw10424step0Labels = mixedMoment B raw10424step1 raw10424step1Labels := by
      have ha : raw10424step1 = (fun i j => raw10424step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10424step1 raw10424step0; decide +kernel
      have hl : raw10424step1Labels = raw10424step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10424step0 raw10424step0Labels permutation39 permutation7
    mixedMoment B raw10424step1 raw10424step1Labels = mixedMoment B raw10424step2 raw10424step2Labels := by
      have ha : raw10424step2 = -raw10424step1 := by apply Matrix.ext; change ∀ i j, raw10424step2 i j = -(raw10424step1 i j); unfold raw10424step2 raw10424step1; decide +kernel
      have hl : raw10424step2Labels = raw10424step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10424step2 raw10424step2Labels = mixedMoment B raw10424step3 raw10424step3Labels := by
      have ha : raw10424step3 = raw10424step2 := by apply Matrix.ext; unfold raw10424step3 raw10424step2; decide +kernel
      have hl : raw10424step2Labels = labelEmbedding1 ∘ raw10424step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10424step2 raw10424step2Labels raw10424step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw10425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10425step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw10425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10425step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10425step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10425step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10425step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10425 raw10425Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw10425 raw10425Labels = mixedMoment B raw10425step0 raw10425step0Labels := by
      have hz : ∀ j, raw10425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10425step0 = (fun i j => raw10425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10425step0 raw10425; decide +kernel
      have hl : raw10425step0Labels = raw10425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10425 raw10425Labels permutation346 hz
    mixedMoment B raw10425step0 raw10425step0Labels = mixedMoment B raw10425step1 raw10425step1Labels := by
      have hz : ∀ j, raw10425step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10425step1 = (fun i j => raw10425step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10425step1 raw10425step0; decide +kernel
      have hl : raw10425step1Labels = raw10425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10425step0 raw10425step0Labels permutation56 hz
    mixedMoment B raw10425step1 raw10425step1Labels = mixedMoment B raw10425step2 raw10425step2Labels := by
      have ha : raw10425step2 = (fun i j => raw10425step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10425step2 raw10425step1; decide +kernel
      have hl : raw10425step2Labels = raw10425step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10425step1 raw10425step1Labels permutation9 permutation7
    mixedMoment B raw10425step2 raw10425step2Labels = mixedMoment B raw10425step3 raw10425step3Labels := by
      have ha : raw10425step3 = -raw10425step2 := by apply Matrix.ext; change ∀ i j, raw10425step3 i j = -(raw10425step2 i j); unfold raw10425step3 raw10425step2; decide +kernel
      have hl : raw10425step3Labels = raw10425step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10425step3 raw10425step3Labels = mixedMoment B raw10425step4 raw10425step4Labels := by
      have ha : raw10425step4 = raw10425step3 := by apply Matrix.ext; unfold raw10425step4 raw10425step3; decide +kernel
      have hl : raw10425step3Labels = labelEmbedding1 ∘ raw10425step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10425step3 raw10425step3Labels raw10425step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3485 node3485Labels := by rfl

def raw10426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10426step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10426step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10426step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10426step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10426step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10426step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10426 raw10426Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw10426 raw10426Labels = mixedMoment B raw10426step0 raw10426step0Labels := by
      have hz : ∀ j, raw10426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10426step0 = (fun i j => raw10426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10426step0 raw10426; decide +kernel
      have hl : raw10426step0Labels = raw10426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10426 raw10426Labels permutation346 hz
    mixedMoment B raw10426step0 raw10426step0Labels = mixedMoment B raw10426step1 raw10426step1Labels := by
      have hz : ∀ j, raw10426step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10426step1 = (fun i j => raw10426step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10426step1 raw10426step0; decide +kernel
      have hl : raw10426step1Labels = raw10426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10426step0 raw10426step0Labels permutation56 hz
    mixedMoment B raw10426step1 raw10426step1Labels = mixedMoment B raw10426step2 raw10426step2Labels := by
      have ha : raw10426step2 = (fun i j => raw10426step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10426step2 raw10426step1; decide +kernel
      have hl : raw10426step2Labels = raw10426step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10426step1 raw10426step1Labels permutation9 permutation7
    mixedMoment B raw10426step2 raw10426step2Labels = mixedMoment B raw10426step3 raw10426step3Labels := by
      have ha : raw10426step3 = -raw10426step2 := by apply Matrix.ext; change ∀ i j, raw10426step3 i j = -(raw10426step2 i j); unfold raw10426step3 raw10426step2; decide +kernel
      have hl : raw10426step3Labels = raw10426step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10426step3 raw10426step3Labels = mixedMoment B raw10426step4 raw10426step4Labels := by
      have ha : raw10426step4 = raw10426step3 := by apply Matrix.ext; unfold raw10426step4 raw10426step3; decide +kernel
      have hl : raw10426step3Labels = labelEmbedding1 ∘ raw10426step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10426step3 raw10426step3Labels raw10426step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw10427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10427step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10427step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10427step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw10427step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10427step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw10427step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10427step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw10427step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10427 raw10427Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw10427 raw10427Labels = mixedMoment B raw10427step0 raw10427step0Labels := by
      have hz : ∀ j, raw10427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10427step0 = (fun i j => raw10427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10427step0 raw10427; decide +kernel
      have hl : raw10427step0Labels = raw10427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10427 raw10427Labels permutation346 hz
    mixedMoment B raw10427step0 raw10427step0Labels = mixedMoment B raw10427step1 raw10427step1Labels := by
      have hz : ∀ j, raw10427step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10427step1 = (fun i j => raw10427step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10427step1 raw10427step0; decide +kernel
      have hl : raw10427step1Labels = raw10427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10427step0 raw10427step0Labels permutation56 hz
    mixedMoment B raw10427step1 raw10427step1Labels = mixedMoment B raw10427step2 raw10427step2Labels := by
      have ha : raw10427step2 = (fun i j => raw10427step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10427step2 raw10427step1; decide +kernel
      have hl : raw10427step2Labels = raw10427step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10427step1 raw10427step1Labels permutation9 permutation7
    mixedMoment B raw10427step2 raw10427step2Labels = mixedMoment B raw10427step3 raw10427step3Labels := by
      have ha : raw10427step3 = -raw10427step2 := by apply Matrix.ext; change ∀ i j, raw10427step3 i j = -(raw10427step2 i j); unfold raw10427step3 raw10427step2; decide +kernel
      have hl : raw10427step3Labels = raw10427step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10427step3 raw10427step3Labels = mixedMoment B raw10427step4 raw10427step4Labels := by
      have ha : raw10427step4 = raw10427step3 := by apply Matrix.ext; unfold raw10427step4 raw10427step3; decide +kernel
      have hl : raw10427step3Labels = labelEmbedding1 ∘ raw10427step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10427step3 raw10427step3Labels raw10427step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw10428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw10428step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10428step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10428step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10428step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10428 raw10428Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw10428 raw10428Labels = mixedMoment B raw10428step0 raw10428step0Labels := by
      have hz : ∀ j, raw10428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10428step0 = (fun i j => raw10428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10428step0 raw10428; decide +kernel
      have hl : raw10428step0Labels = raw10428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10428 raw10428Labels permutation346 hz
    mixedMoment B raw10428step0 raw10428step0Labels = mixedMoment B raw10428step1 raw10428step1Labels := by
      have ha : raw10428step1 = (fun i j => raw10428step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10428step1 raw10428step0; decide +kernel
      have hl : raw10428step1Labels = raw10428step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10428step0 raw10428step0Labels permutation39 permutation7
    mixedMoment B raw10428step1 raw10428step1Labels = mixedMoment B raw10428step2 raw10428step2Labels := by
      have ha : raw10428step2 = -raw10428step1 := by apply Matrix.ext; change ∀ i j, raw10428step2 i j = -(raw10428step1 i j); unfold raw10428step2 raw10428step1; decide +kernel
      have hl : raw10428step2Labels = raw10428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10428step2 raw10428step2Labels = mixedMoment B raw10428step3 raw10428step3Labels := by
      have ha : raw10428step3 = raw10428step2 := by apply Matrix.ext; unfold raw10428step3 raw10428step2; decide +kernel
      have hl : raw10428step2Labels = labelEmbedding1 ∘ raw10428step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10428step2 raw10428step2Labels raw10428step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw10429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw10429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10429step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10429step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10429 raw10429Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw10429 raw10429Labels = mixedMoment B raw10429step0 raw10429step0Labels := by
      have hz : ∀ j, raw10429 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10429step0 = (fun i j => raw10429 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10429step0 raw10429; decide +kernel
      have hl : raw10429step0Labels = raw10429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10429 raw10429Labels permutation265 hz
    mixedMoment B raw10429step0 raw10429step0Labels = mixedMoment B raw10429step1 raw10429step1Labels := by
      have ha : raw10429step1 = (fun i j => raw10429step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10429step1 raw10429step0; decide +kernel
      have hl : raw10429step1Labels = raw10429step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10429step0 raw10429step0Labels permutation39 permutation7
    mixedMoment B raw10429step1 raw10429step1Labels = mixedMoment B raw10429step2 raw10429step2Labels := by
      have ha : raw10429step2 = -raw10429step1 := by apply Matrix.ext; change ∀ i j, raw10429step2 i j = -(raw10429step1 i j); unfold raw10429step2 raw10429step1; decide +kernel
      have hl : raw10429step2Labels = raw10429step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10429step2 raw10429step2Labels = mixedMoment B raw10429step3 raw10429step3Labels := by
      have ha : raw10429step3 = raw10429step2 := by apply Matrix.ext; unfold raw10429step3 raw10429step2; decide +kernel
      have hl : raw10429step2Labels = labelEmbedding1 ∘ raw10429step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10429step2 raw10429step2Labels raw10429step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw10430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10430step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw10430step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10430step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10430step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10430step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10430 raw10430Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw10430 raw10430Labels = mixedMoment B raw10430step0 raw10430step0Labels := by
      have hz : ∀ j, raw10430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10430step0 = (fun i j => raw10430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10430step0 raw10430; decide +kernel
      have hl : raw10430step0Labels = raw10430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10430 raw10430Labels permutation346 hz
    mixedMoment B raw10430step0 raw10430step0Labels = mixedMoment B raw10430step1 raw10430step1Labels := by
      have hz : ∀ j, raw10430step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10430step1 = (fun i j => raw10430step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10430step1 raw10430step0; decide +kernel
      have hl : raw10430step1Labels = raw10430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10430step0 raw10430step0Labels permutation56 hz
    mixedMoment B raw10430step1 raw10430step1Labels = mixedMoment B raw10430step2 raw10430step2Labels := by
      have ha : raw10430step2 = (fun i j => raw10430step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10430step2 raw10430step1; decide +kernel
      have hl : raw10430step2Labels = raw10430step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10430step1 raw10430step1Labels permutation9 permutation7
    mixedMoment B raw10430step2 raw10430step2Labels = mixedMoment B raw10430step3 raw10430step3Labels := by
      have ha : raw10430step3 = -raw10430step2 := by apply Matrix.ext; change ∀ i j, raw10430step3 i j = -(raw10430step2 i j); unfold raw10430step3 raw10430step2; decide +kernel
      have hl : raw10430step3Labels = raw10430step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10430step3 raw10430step3Labels = mixedMoment B raw10430step4 raw10430step4Labels := by
      have ha : raw10430step4 = raw10430step3 := by apply Matrix.ext; unfold raw10430step4 raw10430step3; decide +kernel
      have hl : raw10430step3Labels = labelEmbedding1 ∘ raw10430step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10430step3 raw10430step3Labels raw10430step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

def raw10431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10431step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10431step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw10431step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10431step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw10431step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10431 raw10431Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw10431 raw10431Labels = mixedMoment B raw10431step0 raw10431step0Labels := by
      have hz : ∀ j, raw10431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10431step0 = (fun i j => raw10431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10431step0 raw10431; decide +kernel
      have hl : raw10431step0Labels = raw10431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10431 raw10431Labels permutation346 hz
    mixedMoment B raw10431step0 raw10431step0Labels = mixedMoment B raw10431step1 raw10431step1Labels := by
      have hz : ∀ j, raw10431step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10431step1 = (fun i j => raw10431step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10431step1 raw10431step0; decide +kernel
      have hl : raw10431step1Labels = raw10431step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10431step0 raw10431step0Labels permutation56 hz
    mixedMoment B raw10431step1 raw10431step1Labels = mixedMoment B raw10431step2 raw10431step2Labels := by
      have ha : raw10431step2 = (fun i j => raw10431step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10431step2 raw10431step1; decide +kernel
      have hl : raw10431step2Labels = raw10431step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10431step1 raw10431step1Labels permutation28 permutation5
    mixedMoment B raw10431step2 raw10431step2Labels = mixedMoment B raw10431step3 raw10431step3Labels := by
      have ha : raw10431step3 = raw10431step2 := by apply Matrix.ext; unfold raw10431step3 raw10431step2; decide +kernel
      have hl : raw10431step2Labels = labelEmbedding1 ∘ raw10431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10431step2 raw10431step2Labels raw10431step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw10432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10432 raw10432Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw10432 raw10432Labels = mixedMoment B raw10432step0 raw10432step0Labels := by
      have hz : ∀ j, raw10432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10432step0 = (fun i j => raw10432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10432step0 raw10432; decide +kernel
      have hl : raw10432step0Labels = raw10432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10432 raw10432Labels permutation346 hz
    mixedMoment B raw10432step0 raw10432step0Labels = mixedMoment B raw10432step1 raw10432step1Labels := by
      have hz : ∀ j, raw10432step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10432step1 = (fun i j => raw10432step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10432step1 raw10432step0; decide +kernel
      have hl : raw10432step1Labels = raw10432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10432step0 raw10432step0Labels permutation56 hz
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw10433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10433 raw10433Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw10433 raw10433Labels = mixedMoment B raw10433step0 raw10433step0Labels := by
      have hz : ∀ j, raw10433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10433step0 = (fun i j => raw10433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10433step0 raw10433; decide +kernel
      have hl : raw10433step0Labels = raw10433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10433 raw10433Labels permutation346 hz
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw10434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10434 raw10434Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw10434 raw10434Labels = mixedMoment B raw10434step0 raw10434step0Labels := by
      have hz : ∀ j, raw10434 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10434step0 = (fun i j => raw10434 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10434step0 raw10434; decide +kernel
      have hl : raw10434step0Labels = raw10434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10434 raw10434Labels permutation265 hz
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw10435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10435 raw10435Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw10435 raw10435Labels = mixedMoment B raw10435step0 raw10435step0Labels := by
      have hz : ∀ j, raw10435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10435step0 = (fun i j => raw10435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10435step0 raw10435; decide +kernel
      have hl : raw10435step0Labels = raw10435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10435 raw10435Labels permutation346 hz
    mixedMoment B raw10435step0 raw10435step0Labels = mixedMoment B raw10435step1 raw10435step1Labels := by
      have hz : ∀ j, raw10435step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10435step1 = (fun i j => raw10435step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10435step1 raw10435step0; decide +kernel
      have hl : raw10435step1Labels = raw10435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10435step0 raw10435step0Labels permutation56 hz
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw10436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10436 raw10436Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw10436 raw10436Labels = mixedMoment B raw10436step0 raw10436step0Labels := by
      have hz : ∀ j, raw10436 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10436step0 = (fun i j => raw10436 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10436step0 raw10436; decide +kernel
      have hl : raw10436step0Labels = raw10436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10436 raw10436Labels permutation346 hz
    mixedMoment B raw10436step0 raw10436step0Labels = mixedMoment B raw10436step1 raw10436step1Labels := by
      have hz : ∀ j, raw10436step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10436step1 = (fun i j => raw10436step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10436step1 raw10436step0; decide +kernel
      have hl : raw10436step1Labels = raw10436step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10436step0 raw10436step0Labels permutation56 hz
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw10437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10437step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10437 raw10437Labels = mixedMoment B node3908 node3908Labels := by
  calc
    mixedMoment B raw10437 raw10437Labels = mixedMoment B raw10437step0 raw10437step0Labels := by
      have hz : ∀ j, raw10437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10437step0 = (fun i j => raw10437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10437step0 raw10437; decide +kernel
      have hl : raw10437step0Labels = raw10437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10437 raw10437Labels permutation346 hz
    mixedMoment B raw10437step0 raw10437step0Labels = mixedMoment B raw10437step1 raw10437step1Labels := by
      have hz : ∀ j, raw10437step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10437step1 = (fun i j => raw10437step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10437step1 raw10437step0; decide +kernel
      have hl : raw10437step1Labels = raw10437step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10437step0 raw10437step0Labels permutation56 hz
    mixedMoment B raw10437step1 raw10437step1Labels = mixedMoment B raw10437step2 raw10437step2Labels := by
      have ha : raw10437step2 = (fun i j => raw10437step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10437step2 raw10437step1; decide +kernel
      have hl : raw10437step2Labels = raw10437step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10437step1 raw10437step1Labels permutation9 permutation2
    _ = mixedMoment B node3908 node3908Labels := by rfl

def raw10438 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw10438Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10438step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw10438step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10438step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw10438step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10438step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw10438step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical10438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10438 raw10438Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw10438 raw10438Labels = mixedMoment B raw10438step0 raw10438step0Labels := by
      have hz : ∀ j, raw10438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10438step0 = (fun i j => raw10438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10438step0 raw10438; decide +kernel
      have hl : raw10438step0Labels = raw10438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10438 raw10438Labels permutation346 hz
    mixedMoment B raw10438step0 raw10438step0Labels = mixedMoment B raw10438step1 raw10438step1Labels := by
      have hz : ∀ j, raw10438step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10438step1 = (fun i j => raw10438step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10438step1 raw10438step0; decide +kernel
      have hl : raw10438step1Labels = raw10438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10438step0 raw10438step0Labels permutation56 hz
    mixedMoment B raw10438step1 raw10438step1Labels = mixedMoment B raw10438step2 raw10438step2Labels := by
      have ha : raw10438step2 = (fun i j => raw10438step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw10438step2 raw10438step1; decide +kernel
      have hl : raw10438step2Labels = raw10438step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10438step1 raw10438step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw10439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10439 raw10439Labels = mixedMoment B node2554 node2554Labels := by
  calc
    mixedMoment B raw10439 raw10439Labels = mixedMoment B raw10439step0 raw10439step0Labels := by
      have ha : raw10439step0 = (fun i j => raw10439 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10439step0 raw10439; decide +kernel
      have hl : raw10439step0Labels = raw10439Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10439 raw10439Labels permutation158 permutation2
    _ = mixedMoment B node2554 node2554Labels := by rfl

def raw10440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10440 raw10440Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw10440 raw10440Labels = mixedMoment B raw10440step0 raw10440step0Labels := by
      have hz : ∀ j, raw10440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10440step0 = (fun i j => raw10440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10440step0 raw10440; decide +kernel
      have hl : raw10440step0Labels = raw10440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10440 raw10440Labels permutation346 hz
    _ = mixedMoment B node2591 node2591Labels := by rfl

def raw10441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10441 raw10441Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw10441 raw10441Labels = mixedMoment B raw10441step0 raw10441step0Labels := by
      have hz : ∀ j, raw10441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10441step0 = (fun i j => raw10441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10441step0 raw10441; decide +kernel
      have hl : raw10441step0Labels = raw10441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10441 raw10441Labels permutation346 hz
    mixedMoment B raw10441step0 raw10441step0Labels = mixedMoment B raw10441step1 raw10441step1Labels := by
      have ha : raw10441step1 = (fun i j => raw10441step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10441step1 raw10441step0; decide +kernel
      have hl : raw10441step1Labels = raw10441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10441step0 raw10441step0Labels permutation33 permutation2
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw10442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10442 raw10442Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw10442 raw10442Labels = mixedMoment B raw10442step0 raw10442step0Labels := by
      have hz : ∀ j, raw10442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10442step0 = (fun i j => raw10442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10442step0 raw10442; decide +kernel
      have hl : raw10442step0Labels = raw10442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10442 raw10442Labels permutation346 hz
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw10443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10443 raw10443Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw10443 raw10443Labels = mixedMoment B raw10443step0 raw10443step0Labels := by
      have hz : ∀ j, raw10443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10443step0 = (fun i j => raw10443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10443step0 raw10443; decide +kernel
      have hl : raw10443step0Labels = raw10443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10443 raw10443Labels permutation346 hz
    mixedMoment B raw10443step0 raw10443step0Labels = mixedMoment B raw10443step1 raw10443step1Labels := by
      have ha : raw10443step1 = (fun i j => raw10443step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10443step1 raw10443step0; decide +kernel
      have hl : raw10443step1Labels = raw10443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10443step0 raw10443step0Labels permutation38 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw10444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10444 raw10444Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw10444 raw10444Labels = mixedMoment B raw10444step0 raw10444step0Labels := by
      have hz : ∀ j, raw10444 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10444step0 = (fun i j => raw10444 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10444step0 raw10444; decide +kernel
      have hl : raw10444step0Labels = raw10444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10444 raw10444Labels permutation265 hz
    mixedMoment B raw10444step0 raw10444step0Labels = mixedMoment B raw10444step1 raw10444step1Labels := by
      have ha : raw10444step1 = (fun i j => raw10444step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10444step1 raw10444step0; decide +kernel
      have hl : raw10444step1Labels = raw10444step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10444step0 raw10444step0Labels permutation38 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw10445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10445 raw10445Labels = mixedMoment B node2523 node2523Labels := by
  calc
    mixedMoment B raw10445 raw10445Labels = mixedMoment B raw10445step0 raw10445step0Labels := by
      have hz : ∀ j, raw10445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10445step0 = (fun i j => raw10445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10445step0 raw10445; decide +kernel
      have hl : raw10445step0Labels = raw10445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10445 raw10445Labels permutation346 hz
    mixedMoment B raw10445step0 raw10445step0Labels = mixedMoment B raw10445step1 raw10445step1Labels := by
      have hz : ∀ j, raw10445step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10445step1 = (fun i j => raw10445step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10445step1 raw10445step0; decide +kernel
      have hl : raw10445step1Labels = raw10445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10445step0 raw10445step0Labels permutation56 hz
    mixedMoment B raw10445step1 raw10445step1Labels = mixedMoment B raw10445step2 raw10445step2Labels := by
      have ha : raw10445step2 = (fun i j => raw10445step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10445step2 raw10445step1; decide +kernel
      have hl : raw10445step2Labels = raw10445step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10445step1 raw10445step1Labels permutation9 permutation2
    _ = mixedMoment B node2523 node2523Labels := by rfl

def raw10446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10446 raw10446Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw10446 raw10446Labels = mixedMoment B raw10446step0 raw10446step0Labels := by
      have hz : ∀ j, raw10446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10446step0 = (fun i j => raw10446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10446step0 raw10446; decide +kernel
      have hl : raw10446step0Labels = raw10446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10446 raw10446Labels permutation346 hz
    mixedMoment B raw10446step0 raw10446step0Labels = mixedMoment B raw10446step1 raw10446step1Labels := by
      have hz : ∀ j, raw10446step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10446step1 = (fun i j => raw10446step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10446step1 raw10446step0; decide +kernel
      have hl : raw10446step1Labels = raw10446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10446step0 raw10446step0Labels permutation56 hz
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw10447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10447 raw10447Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw10447 raw10447Labels = mixedMoment B raw10447step0 raw10447step0Labels := by
      have hz : ∀ j, raw10447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10447step0 = (fun i j => raw10447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10447step0 raw10447; decide +kernel
      have hl : raw10447step0Labels = raw10447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10447 raw10447Labels permutation346 hz
    mixedMoment B raw10447step0 raw10447step0Labels = mixedMoment B raw10447step1 raw10447step1Labels := by
      have hz : ∀ j, raw10447step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10447step1 = (fun i j => raw10447step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10447step1 raw10447step0; decide +kernel
      have hl : raw10447step1Labels = raw10447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10447step0 raw10447step0Labels permutation56 hz
    mixedMoment B raw10447step1 raw10447step1Labels = mixedMoment B raw10447step2 raw10447step2Labels := by
      have ha : raw10447step2 = (fun i j => raw10447step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10447step2 raw10447step1; decide +kernel
      have hl : raw10447step2Labels = raw10447step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10447step1 raw10447step1Labels permutation9 permutation2
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw10448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10448 raw10448Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw10448 raw10448Labels = mixedMoment B raw10448step0 raw10448step0Labels := by
      have hz : ∀ j, raw10448 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10448step0 = (fun i j => raw10448 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10448step0 raw10448; decide +kernel
      have hl : raw10448step0Labels = raw10448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10448 raw10448Labels permutation265 hz
    mixedMoment B raw10448step0 raw10448step0Labels = mixedMoment B raw10448step1 raw10448step1Labels := by
      have ha : raw10448step1 = (fun i j => raw10448step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10448step1 raw10448step0; decide +kernel
      have hl : raw10448step1Labels = raw10448step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10448step0 raw10448step0Labels permutation33 permutation2
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw10449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10449 raw10449Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw10449 raw10449Labels = mixedMoment B raw10449step0 raw10449step0Labels := by
      have hz : ∀ j, raw10449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10449step0 = (fun i j => raw10449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10449step0 raw10449; decide +kernel
      have hl : raw10449step0Labels = raw10449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10449 raw10449Labels permutation346 hz
    mixedMoment B raw10449step0 raw10449step0Labels = mixedMoment B raw10449step1 raw10449step1Labels := by
      have hz : ∀ j, raw10449step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10449step1 = (fun i j => raw10449step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10449step1 raw10449step0; decide +kernel
      have hl : raw10449step1Labels = raw10449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10449step0 raw10449step0Labels permutation56 hz
    mixedMoment B raw10449step1 raw10449step1Labels = mixedMoment B raw10449step2 raw10449step2Labels := by
      have ha : raw10449step2 = (fun i j => raw10449step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10449step2 raw10449step1; decide +kernel
      have hl : raw10449step2Labels = raw10449step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10449step1 raw10449step1Labels permutation9 permutation2
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw10450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10450step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10450step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10450step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10450 raw10450Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw10450 raw10450Labels = mixedMoment B raw10450step0 raw10450step0Labels := by
      have hz : ∀ j, raw10450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10450step0 = (fun i j => raw10450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10450step0 raw10450; decide +kernel
      have hl : raw10450step0Labels = raw10450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10450 raw10450Labels permutation346 hz
    mixedMoment B raw10450step0 raw10450step0Labels = mixedMoment B raw10450step1 raw10450step1Labels := by
      have ha : raw10450step1 = (fun i j => raw10450step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10450step1 raw10450step0; decide +kernel
      have hl : raw10450step1Labels = raw10450step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10450step0 raw10450step0Labels permutation151 permutation3
    mixedMoment B raw10450step1 raw10450step1Labels = mixedMoment B raw10450step2 raw10450step2Labels := by
      have ha : raw10450step2 = -raw10450step1 := by apply Matrix.ext; change ∀ i j, raw10450step2 i j = -(raw10450step1 i j); unfold raw10450step2 raw10450step1; decide +kernel
      have hl : raw10450step2Labels = raw10450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10450step2 raw10450step2Labels = mixedMoment B raw10450step3 raw10450step3Labels := by
      have ha : raw10450step3 = raw10450step2 := by apply Matrix.ext; unfold raw10450step3 raw10450step2; decide +kernel
      have hl : raw10450step2Labels = labelEmbedding6 ∘ raw10450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10450step2 raw10450step2Labels raw10450step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw10451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10451step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10451step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10451step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10451step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10451 raw10451Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw10451 raw10451Labels = mixedMoment B raw10451step0 raw10451step0Labels := by
      have hz : ∀ j, raw10451 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10451step0 = (fun i j => raw10451 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10451step0 raw10451; decide +kernel
      have hl : raw10451step0Labels = raw10451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10451 raw10451Labels permutation265 hz
    mixedMoment B raw10451step0 raw10451step0Labels = mixedMoment B raw10451step1 raw10451step1Labels := by
      have ha : raw10451step1 = (fun i j => raw10451step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10451step1 raw10451step0; decide +kernel
      have hl : raw10451step1Labels = raw10451step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10451step0 raw10451step0Labels permutation151 permutation3
    mixedMoment B raw10451step1 raw10451step1Labels = mixedMoment B raw10451step2 raw10451step2Labels := by
      have ha : raw10451step2 = -raw10451step1 := by apply Matrix.ext; change ∀ i j, raw10451step2 i j = -(raw10451step1 i j); unfold raw10451step2 raw10451step1; decide +kernel
      have hl : raw10451step2Labels = raw10451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10451step2 raw10451step2Labels = mixedMoment B raw10451step3 raw10451step3Labels := by
      have ha : raw10451step3 = raw10451step2 := by apply Matrix.ext; unfold raw10451step3 raw10451step2; decide +kernel
      have hl : raw10451step2Labels = labelEmbedding6 ∘ raw10451step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10451step2 raw10451step2Labels raw10451step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw10452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10452step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw10452step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw10452step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10452 raw10452Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw10452 raw10452Labels = mixedMoment B raw10452step0 raw10452step0Labels := by
      have hz : ∀ j, raw10452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10452step0 = (fun i j => raw10452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10452step0 raw10452; decide +kernel
      have hl : raw10452step0Labels = raw10452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10452 raw10452Labels permutation346 hz
    mixedMoment B raw10452step0 raw10452step0Labels = mixedMoment B raw10452step1 raw10452step1Labels := by
      have hz : ∀ j, raw10452step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10452step1 = (fun i j => raw10452step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10452step1 raw10452step0; decide +kernel
      have hl : raw10452step1Labels = raw10452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10452step0 raw10452step0Labels permutation56 hz
    mixedMoment B raw10452step1 raw10452step1Labels = mixedMoment B raw10452step2 raw10452step2Labels := by
      have ha : raw10452step2 = (fun i j => raw10452step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10452step2 raw10452step1; decide +kernel
      have hl : raw10452step2Labels = raw10452step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10452step1 raw10452step1Labels permutation8 permutation3
    mixedMoment B raw10452step2 raw10452step2Labels = mixedMoment B raw10452step3 raw10452step3Labels := by
      have ha : raw10452step3 = raw10452step2 := by apply Matrix.ext; unfold raw10452step3 raw10452step2; decide +kernel
      have hl : raw10452step2Labels = labelEmbedding6 ∘ raw10452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10452step2 raw10452step2Labels raw10452step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw10453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw10453step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10453 raw10453Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw10453 raw10453Labels = mixedMoment B raw10453step0 raw10453step0Labels := by
      have hz : ∀ j, raw10453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10453step0 = (fun i j => raw10453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10453step0 raw10453; decide +kernel
      have hl : raw10453step0Labels = raw10453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10453 raw10453Labels permutation346 hz
    mixedMoment B raw10453step0 raw10453step0Labels = mixedMoment B raw10453step1 raw10453step1Labels := by
      have hz : ∀ j, raw10453step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10453step1 = (fun i j => raw10453step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10453step1 raw10453step0; decide +kernel
      have hl : raw10453step1Labels = raw10453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10453step0 raw10453step0Labels permutation56 hz
    mixedMoment B raw10453step1 raw10453step1Labels = mixedMoment B raw10453step2 raw10453step2Labels := by
      have ha : raw10453step2 = (fun i j => raw10453step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10453step2 raw10453step1; decide +kernel
      have hl : raw10453step2Labels = raw10453step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10453step1 raw10453step1Labels permutation10 permutation2
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw10454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10454step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10454step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10454 raw10454Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw10454 raw10454Labels = mixedMoment B raw10454step0 raw10454step0Labels := by
      have hz : ∀ j, raw10454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10454step0 = (fun i j => raw10454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10454step0 raw10454; decide +kernel
      have hl : raw10454step0Labels = raw10454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10454 raw10454Labels permutation346 hz
    mixedMoment B raw10454step0 raw10454step0Labels = mixedMoment B raw10454step1 raw10454step1Labels := by
      have hz : ∀ j, raw10454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10454step1 = (fun i j => raw10454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10454step1 raw10454step0; decide +kernel
      have hl : raw10454step1Labels = raw10454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10454step0 raw10454step0Labels permutation56 hz
    mixedMoment B raw10454step1 raw10454step1Labels = mixedMoment B raw10454step2 raw10454step2Labels := by
      have ha : raw10454step2 = (fun i j => raw10454step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10454step2 raw10454step1; decide +kernel
      have hl : raw10454step2Labels = raw10454step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10454step1 raw10454step1Labels permutation9 permutation3
    mixedMoment B raw10454step2 raw10454step2Labels = mixedMoment B raw10454step3 raw10454step3Labels := by
      have ha : raw10454step3 = raw10454step2 := by apply Matrix.ext; unfold raw10454step3 raw10454step2; decide +kernel
      have hl : raw10454step2Labels = labelEmbedding6 ∘ raw10454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10454step2 raw10454step2Labels raw10454step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw10455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10455step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10455 raw10455Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw10455 raw10455Labels = mixedMoment B raw10455step0 raw10455step0Labels := by
      have hz : ∀ j, raw10455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10455step0 = (fun i j => raw10455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10455step0 raw10455; decide +kernel
      have hl : raw10455step0Labels = raw10455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10455 raw10455Labels permutation346 hz
    mixedMoment B raw10455step0 raw10455step0Labels = mixedMoment B raw10455step1 raw10455step1Labels := by
      have ha : raw10455step1 = (fun i j => raw10455step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10455step1 raw10455step0; decide +kernel
      have hl : raw10455step1Labels = raw10455step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10455step0 raw10455step0Labels permutation38 permutation3
    mixedMoment B raw10455step1 raw10455step1Labels = mixedMoment B raw10455step2 raw10455step2Labels := by
      have ha : raw10455step2 = raw10455step1 := by apply Matrix.ext; unfold raw10455step2 raw10455step1; decide +kernel
      have hl : raw10455step1Labels = labelEmbedding6 ∘ raw10455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10455step1 raw10455step1Labels raw10455step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw10456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10456step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10456step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10456 raw10456Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw10456 raw10456Labels = mixedMoment B raw10456step0 raw10456step0Labels := by
      have ha : raw10456step0 = (fun i j => raw10456 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10456step0 raw10456; decide +kernel
      have hl : raw10456step0Labels = raw10456Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10456 raw10456Labels permutation182 permutation3
    mixedMoment B raw10456step0 raw10456step0Labels = mixedMoment B raw10456step1 raw10456step1Labels := by
      have ha : raw10456step1 = raw10456step0 := by apply Matrix.ext; unfold raw10456step1 raw10456step0; decide +kernel
      have hl : raw10456step0Labels = labelEmbedding6 ∘ raw10456step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10456step0 raw10456step0Labels raw10456step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw10457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10457step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10457 raw10457Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw10457 raw10457Labels = mixedMoment B raw10457step0 raw10457step0Labels := by
      have hz : ∀ j, raw10457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10457step0 = (fun i j => raw10457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10457step0 raw10457; decide +kernel
      have hl : raw10457step0Labels = raw10457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10457 raw10457Labels permutation346 hz
    mixedMoment B raw10457step0 raw10457step0Labels = mixedMoment B raw10457step1 raw10457step1Labels := by
      have ha : raw10457step1 = (fun i j => raw10457step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10457step1 raw10457step0; decide +kernel
      have hl : raw10457step1Labels = raw10457step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10457step0 raw10457step0Labels permutation38 permutation3
    mixedMoment B raw10457step1 raw10457step1Labels = mixedMoment B raw10457step2 raw10457step2Labels := by
      have ha : raw10457step2 = raw10457step1 := by apply Matrix.ext; unfold raw10457step2 raw10457step1; decide +kernel
      have hl : raw10457step1Labels = labelEmbedding6 ∘ raw10457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10457step1 raw10457step1Labels raw10457step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw10458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10458step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10458 raw10458Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw10458 raw10458Labels = mixedMoment B raw10458step0 raw10458step0Labels := by
      have hz : ∀ j, raw10458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10458step0 = (fun i j => raw10458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10458step0 raw10458; decide +kernel
      have hl : raw10458step0Labels = raw10458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10458 raw10458Labels permutation346 hz
    mixedMoment B raw10458step0 raw10458step0Labels = mixedMoment B raw10458step1 raw10458step1Labels := by
      have ha : raw10458step1 = (fun i j => raw10458step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10458step1 raw10458step0; decide +kernel
      have hl : raw10458step1Labels = raw10458step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10458step0 raw10458step0Labels permutation40 permutation3
    mixedMoment B raw10458step1 raw10458step1Labels = mixedMoment B raw10458step2 raw10458step2Labels := by
      have ha : raw10458step2 = raw10458step1 := by apply Matrix.ext; unfold raw10458step2 raw10458step1; decide +kernel
      have hl : raw10458step1Labels = labelEmbedding6 ∘ raw10458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10458step1 raw10458step1Labels raw10458step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw10459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10459step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10459step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10459step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10459 raw10459Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10459 raw10459Labels = mixedMoment B raw10459step0 raw10459step0Labels := by
      have hz : ∀ j, raw10459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10459step0 = (fun i j => raw10459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10459step0 raw10459; decide +kernel
      have hl : raw10459step0Labels = raw10459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10459 raw10459Labels permutation346 hz
    mixedMoment B raw10459step0 raw10459step0Labels = mixedMoment B raw10459step1 raw10459step1Labels := by
      have ha : raw10459step1 = (fun i j => raw10459step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10459step1 raw10459step0; decide +kernel
      have hl : raw10459step1Labels = raw10459step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10459step0 raw10459step0Labels permutation42 permutation3
    mixedMoment B raw10459step1 raw10459step1Labels = mixedMoment B raw10459step2 raw10459step2Labels := by
      have ha : raw10459step2 = raw10459step1 := by apply Matrix.ext; unfold raw10459step2 raw10459step1; decide +kernel
      have hl : raw10459step1Labels = labelEmbedding6 ∘ raw10459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10459step1 raw10459step1Labels raw10459step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10460step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10460step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10460 raw10460Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw10460 raw10460Labels = mixedMoment B raw10460step0 raw10460step0Labels := by
      have hz : ∀ j, raw10460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10460step0 = (fun i j => raw10460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10460step0 raw10460; decide +kernel
      have hl : raw10460step0Labels = raw10460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10460 raw10460Labels permutation265 hz
    mixedMoment B raw10460step0 raw10460step0Labels = mixedMoment B raw10460step1 raw10460step1Labels := by
      have ha : raw10460step1 = (fun i j => raw10460step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10460step1 raw10460step0; decide +kernel
      have hl : raw10460step1Labels = raw10460step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10460step0 raw10460step0Labels permutation38 permutation3
    mixedMoment B raw10460step1 raw10460step1Labels = mixedMoment B raw10460step2 raw10460step2Labels := by
      have ha : raw10460step2 = raw10460step1 := by apply Matrix.ext; unfold raw10460step2 raw10460step1; decide +kernel
      have hl : raw10460step1Labels = labelEmbedding6 ∘ raw10460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10460step1 raw10460step1Labels raw10460step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw10461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10461 raw10461Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw10461 raw10461Labels = mixedMoment B raw10461step0 raw10461step0Labels := by
      have ha : raw10461step0 = (fun i j => raw10461 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10461step0 raw10461; decide +kernel
      have hl : raw10461step0Labels = raw10461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10461 raw10461Labels permutation158 permutation3
    mixedMoment B raw10461step0 raw10461step0Labels = mixedMoment B raw10461step1 raw10461step1Labels := by
      have ha : raw10461step1 = raw10461step0 := by apply Matrix.ext; unfold raw10461step1 raw10461step0; decide +kernel
      have hl : raw10461step0Labels = labelEmbedding6 ∘ raw10461step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10461step0 raw10461step0Labels raw10461step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw10462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10462step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10462 raw10462Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw10462 raw10462Labels = mixedMoment B raw10462step0 raw10462step0Labels := by
      have hz : ∀ j, raw10462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10462step0 = (fun i j => raw10462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10462step0 raw10462; decide +kernel
      have hl : raw10462step0Labels = raw10462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10462 raw10462Labels permutation265 hz
    mixedMoment B raw10462step0 raw10462step0Labels = mixedMoment B raw10462step1 raw10462step1Labels := by
      have ha : raw10462step1 = (fun i j => raw10462step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10462step1 raw10462step0; decide +kernel
      have hl : raw10462step1Labels = raw10462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10462step0 raw10462step0Labels permutation38 permutation3
    mixedMoment B raw10462step1 raw10462step1Labels = mixedMoment B raw10462step2 raw10462step2Labels := by
      have ha : raw10462step2 = raw10462step1 := by apply Matrix.ext; unfold raw10462step2 raw10462step1; decide +kernel
      have hl : raw10462step1Labels = labelEmbedding6 ∘ raw10462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10462step1 raw10462step1Labels raw10462step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw10463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10463step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10463 raw10463Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw10463 raw10463Labels = mixedMoment B raw10463step0 raw10463step0Labels := by
      have hz : ∀ j, raw10463 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10463step0 = (fun i j => raw10463 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10463step0 raw10463; decide +kernel
      have hl : raw10463step0Labels = raw10463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10463 raw10463Labels permutation265 hz
    mixedMoment B raw10463step0 raw10463step0Labels = mixedMoment B raw10463step1 raw10463step1Labels := by
      have ha : raw10463step1 = (fun i j => raw10463step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10463step1 raw10463step0; decide +kernel
      have hl : raw10463step1Labels = raw10463step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10463step0 raw10463step0Labels permutation40 permutation3
    mixedMoment B raw10463step1 raw10463step1Labels = mixedMoment B raw10463step2 raw10463step2Labels := by
      have ha : raw10463step2 = raw10463step1 := by apply Matrix.ext; unfold raw10463step2 raw10463step1; decide +kernel
      have hl : raw10463step1Labels = labelEmbedding6 ∘ raw10463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10463step1 raw10463step1Labels raw10463step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw10464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10464step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10464step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10464 raw10464Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10464 raw10464Labels = mixedMoment B raw10464step0 raw10464step0Labels := by
      have hz : ∀ j, raw10464 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10464step0 = (fun i j => raw10464 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10464step0 raw10464; decide +kernel
      have hl : raw10464step0Labels = raw10464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10464 raw10464Labels permutation265 hz
    mixedMoment B raw10464step0 raw10464step0Labels = mixedMoment B raw10464step1 raw10464step1Labels := by
      have ha : raw10464step1 = (fun i j => raw10464step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10464step1 raw10464step0; decide +kernel
      have hl : raw10464step1Labels = raw10464step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10464step0 raw10464step0Labels permutation42 permutation3
    mixedMoment B raw10464step1 raw10464step1Labels = mixedMoment B raw10464step2 raw10464step2Labels := by
      have ha : raw10464step2 = raw10464step1 := by apply Matrix.ext; unfold raw10464step2 raw10464step1; decide +kernel
      have hl : raw10464step1Labels = labelEmbedding6 ∘ raw10464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10464step1 raw10464step1Labels raw10464step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10465step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10465step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10465step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10465step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10465 raw10465Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw10465 raw10465Labels = mixedMoment B raw10465step0 raw10465step0Labels := by
      have hz : ∀ j, raw10465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10465step0 = (fun i j => raw10465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10465step0 raw10465; decide +kernel
      have hl : raw10465step0Labels = raw10465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10465 raw10465Labels permutation346 hz
    mixedMoment B raw10465step0 raw10465step0Labels = mixedMoment B raw10465step1 raw10465step1Labels := by
      have hz : ∀ j, raw10465step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10465step1 = (fun i j => raw10465step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10465step1 raw10465step0; decide +kernel
      have hl : raw10465step1Labels = raw10465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10465step0 raw10465step0Labels permutation56 hz
    mixedMoment B raw10465step1 raw10465step1Labels = mixedMoment B raw10465step2 raw10465step2Labels := by
      have ha : raw10465step2 = (fun i j => raw10465step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10465step2 raw10465step1; decide +kernel
      have hl : raw10465step2Labels = raw10465step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10465step1 raw10465step1Labels permutation8 permutation3
    mixedMoment B raw10465step2 raw10465step2Labels = mixedMoment B raw10465step3 raw10465step3Labels := by
      have ha : raw10465step3 = raw10465step2 := by apply Matrix.ext; unfold raw10465step3 raw10465step2; decide +kernel
      have hl : raw10465step2Labels = labelEmbedding6 ∘ raw10465step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10465step2 raw10465step2Labels raw10465step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw10466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10466step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10466 raw10466Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw10466 raw10466Labels = mixedMoment B raw10466step0 raw10466step0Labels := by
      have hz : ∀ j, raw10466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10466step0 = (fun i j => raw10466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10466step0 raw10466; decide +kernel
      have hl : raw10466step0Labels = raw10466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10466 raw10466Labels permutation346 hz
    mixedMoment B raw10466step0 raw10466step0Labels = mixedMoment B raw10466step1 raw10466step1Labels := by
      have ha : raw10466step1 = (fun i j => raw10466step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10466step1 raw10466step0; decide +kernel
      have hl : raw10466step1Labels = raw10466step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10466step0 raw10466step0Labels permutation32 permutation3
    mixedMoment B raw10466step1 raw10466step1Labels = mixedMoment B raw10466step2 raw10466step2Labels := by
      have ha : raw10466step2 = raw10466step1 := by apply Matrix.ext; unfold raw10466step2 raw10466step1; decide +kernel
      have hl : raw10466step1Labels = labelEmbedding6 ∘ raw10466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10466step1 raw10466step1Labels raw10466step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw10467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10467step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10467step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10467 raw10467Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw10467 raw10467Labels = mixedMoment B raw10467step0 raw10467step0Labels := by
      have hz : ∀ j, raw10467 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10467step0 = (fun i j => raw10467 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10467step0 raw10467; decide +kernel
      have hl : raw10467step0Labels = raw10467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10467 raw10467Labels permutation265 hz
    mixedMoment B raw10467step0 raw10467step0Labels = mixedMoment B raw10467step1 raw10467step1Labels := by
      have ha : raw10467step1 = (fun i j => raw10467step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10467step1 raw10467step0; decide +kernel
      have hl : raw10467step1Labels = raw10467step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10467step0 raw10467step0Labels permutation32 permutation3
    mixedMoment B raw10467step1 raw10467step1Labels = mixedMoment B raw10467step2 raw10467step2Labels := by
      have ha : raw10467step2 = raw10467step1 := by apply Matrix.ext; unfold raw10467step2 raw10467step1; decide +kernel
      have hl : raw10467step1Labels = labelEmbedding6 ∘ raw10467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10467step1 raw10467step1Labels raw10467step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw10468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10468step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10468step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10468 raw10468Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw10468 raw10468Labels = mixedMoment B raw10468step0 raw10468step0Labels := by
      have hz : ∀ j, raw10468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10468step0 = (fun i j => raw10468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10468step0 raw10468; decide +kernel
      have hl : raw10468step0Labels = raw10468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10468 raw10468Labels permutation346 hz
    mixedMoment B raw10468step0 raw10468step0Labels = mixedMoment B raw10468step1 raw10468step1Labels := by
      have hz : ∀ j, raw10468step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10468step1 = (fun i j => raw10468step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10468step1 raw10468step0; decide +kernel
      have hl : raw10468step1Labels = raw10468step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10468step0 raw10468step0Labels permutation56 hz
    mixedMoment B raw10468step1 raw10468step1Labels = mixedMoment B raw10468step2 raw10468step2Labels := by
      have ha : raw10468step2 = (fun i j => raw10468step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10468step2 raw10468step1; decide +kernel
      have hl : raw10468step2Labels = raw10468step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10468step1 raw10468step1Labels permutation10 permutation3
    mixedMoment B raw10468step2 raw10468step2Labels = mixedMoment B raw10468step3 raw10468step3Labels := by
      have ha : raw10468step3 = raw10468step2 := by apply Matrix.ext; unfold raw10468step3 raw10468step2; decide +kernel
      have hl : raw10468step2Labels = labelEmbedding6 ∘ raw10468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10468step2 raw10468step2Labels raw10468step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw10469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10469step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10469step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10469step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10469 raw10469Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw10469 raw10469Labels = mixedMoment B raw10469step0 raw10469step0Labels := by
      have hz : ∀ j, raw10469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10469step0 = (fun i j => raw10469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10469step0 raw10469; decide +kernel
      have hl : raw10469step0Labels = raw10469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10469 raw10469Labels permutation346 hz
    mixedMoment B raw10469step0 raw10469step0Labels = mixedMoment B raw10469step1 raw10469step1Labels := by
      have hz : ∀ j, raw10469step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10469step1 = (fun i j => raw10469step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10469step1 raw10469step0; decide +kernel
      have hl : raw10469step1Labels = raw10469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10469step0 raw10469step0Labels permutation56 hz
    mixedMoment B raw10469step1 raw10469step1Labels = mixedMoment B raw10469step2 raw10469step2Labels := by
      have ha : raw10469step2 = (fun i j => raw10469step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10469step2 raw10469step1; decide +kernel
      have hl : raw10469step2Labels = raw10469step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10469step1 raw10469step1Labels permutation9 permutation3
    mixedMoment B raw10469step2 raw10469step2Labels = mixedMoment B raw10469step3 raw10469step3Labels := by
      have ha : raw10469step3 = raw10469step2 := by apply Matrix.ext; unfold raw10469step3 raw10469step2; decide +kernel
      have hl : raw10469step2Labels = labelEmbedding6 ∘ raw10469step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10469step2 raw10469step2Labels raw10469step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw10470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10470step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10470step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10470step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10470step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10470 raw10470Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw10470 raw10470Labels = mixedMoment B raw10470step0 raw10470step0Labels := by
      have hz : ∀ j, raw10470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10470step0 = (fun i j => raw10470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10470step0 raw10470; decide +kernel
      have hl : raw10470step0Labels = raw10470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10470 raw10470Labels permutation346 hz
    mixedMoment B raw10470step0 raw10470step0Labels = mixedMoment B raw10470step1 raw10470step1Labels := by
      have hz : ∀ j, raw10470step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10470step1 = (fun i j => raw10470step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10470step1 raw10470step0; decide +kernel
      have hl : raw10470step1Labels = raw10470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10470step0 raw10470step0Labels permutation56 hz
    mixedMoment B raw10470step1 raw10470step1Labels = mixedMoment B raw10470step2 raw10470step2Labels := by
      have ha : raw10470step2 = (fun i j => raw10470step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10470step2 raw10470step1; decide +kernel
      have hl : raw10470step2Labels = raw10470step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10470step1 raw10470step1Labels permutation9 permutation3
    mixedMoment B raw10470step2 raw10470step2Labels = mixedMoment B raw10470step3 raw10470step3Labels := by
      have ha : raw10470step3 = raw10470step2 := by apply Matrix.ext; unfold raw10470step3 raw10470step2; decide +kernel
      have hl : raw10470step2Labels = labelEmbedding6 ∘ raw10470step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10470step2 raw10470step2Labels raw10470step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw10471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10471step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10471step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10471 raw10471Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw10471 raw10471Labels = mixedMoment B raw10471step0 raw10471step0Labels := by
      have hz : ∀ j, raw10471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10471step0 = (fun i j => raw10471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10471step0 raw10471; decide +kernel
      have hl : raw10471step0Labels = raw10471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10471 raw10471Labels permutation346 hz
    mixedMoment B raw10471step0 raw10471step0Labels = mixedMoment B raw10471step1 raw10471step1Labels := by
      have ha : raw10471step1 = (fun i j => raw10471step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10471step1 raw10471step0; decide +kernel
      have hl : raw10471step1Labels = raw10471step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10471step0 raw10471step0Labels permutation127 permutation5
    mixedMoment B raw10471step1 raw10471step1Labels = mixedMoment B raw10471step2 raw10471step2Labels := by
      have ha : raw10471step2 = raw10471step1 := by apply Matrix.ext; unfold raw10471step2 raw10471step1; decide +kernel
      have hl : raw10471step1Labels = labelEmbedding8 ∘ raw10471step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10471step1 raw10471step1Labels raw10471step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw10472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10472step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw10472step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10472 raw10472Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw10472 raw10472Labels = mixedMoment B raw10472step0 raw10472step0Labels := by
      have hz : ∀ j, raw10472 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10472step0 = (fun i j => raw10472 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10472step0 raw10472; decide +kernel
      have hl : raw10472step0Labels = raw10472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10472 raw10472Labels permutation265 hz
    mixedMoment B raw10472step0 raw10472step0Labels = mixedMoment B raw10472step1 raw10472step1Labels := by
      have ha : raw10472step1 = (fun i j => raw10472step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10472step1 raw10472step0; decide +kernel
      have hl : raw10472step1Labels = raw10472step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10472step0 raw10472step0Labels permutation127 permutation5
    mixedMoment B raw10472step1 raw10472step1Labels = mixedMoment B raw10472step2 raw10472step2Labels := by
      have ha : raw10472step2 = raw10472step1 := by apply Matrix.ext; unfold raw10472step2 raw10472step1; decide +kernel
      have hl : raw10472step1Labels = labelEmbedding8 ∘ raw10472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10472step1 raw10472step1Labels raw10472step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw10473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10473step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw10473step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10473step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw10473step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10473 raw10473Labels = mixedMoment B node5023 node5023Labels := by
  calc
    mixedMoment B raw10473 raw10473Labels = mixedMoment B raw10473step0 raw10473step0Labels := by
      have hz : ∀ j, raw10473 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10473step0 = (fun i j => raw10473 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10473step0 raw10473; decide +kernel
      have hl : raw10473step0Labels = raw10473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10473 raw10473Labels permutation346 hz
    mixedMoment B raw10473step0 raw10473step0Labels = mixedMoment B raw10473step1 raw10473step1Labels := by
      have hz : ∀ j, raw10473step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10473step1 = (fun i j => raw10473step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10473step1 raw10473step0; decide +kernel
      have hl : raw10473step1Labels = raw10473step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10473step0 raw10473step0Labels permutation56 hz
    mixedMoment B raw10473step1 raw10473step1Labels = mixedMoment B raw10473step2 raw10473step2Labels := by
      have ha : raw10473step2 = (fun i j => raw10473step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10473step2 raw10473step1; decide +kernel
      have hl : raw10473step2Labels = raw10473step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10473step1 raw10473step1Labels permutation9 permutation3
    mixedMoment B raw10473step2 raw10473step2Labels = mixedMoment B raw10473step3 raw10473step3Labels := by
      have ha : raw10473step3 = raw10473step2 := by apply Matrix.ext; unfold raw10473step3 raw10473step2; decide +kernel
      have hl : raw10473step2Labels = labelEmbedding6 ∘ raw10473step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10473step2 raw10473step2Labels raw10473step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5023 node5023Labels := by rfl

def raw10474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10474step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10474step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10474step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10474 raw10474Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw10474 raw10474Labels = mixedMoment B raw10474step0 raw10474step0Labels := by
      have hz : ∀ j, raw10474 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10474step0 = (fun i j => raw10474 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10474step0 raw10474; decide +kernel
      have hl : raw10474step0Labels = raw10474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10474 raw10474Labels permutation346 hz
    mixedMoment B raw10474step0 raw10474step0Labels = mixedMoment B raw10474step1 raw10474step1Labels := by
      have hz : ∀ j, raw10474step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10474step1 = (fun i j => raw10474step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10474step1 raw10474step0; decide +kernel
      have hl : raw10474step1Labels = raw10474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10474step0 raw10474step0Labels permutation56 hz
    mixedMoment B raw10474step1 raw10474step1Labels = mixedMoment B raw10474step2 raw10474step2Labels := by
      have ha : raw10474step2 = (fun i j => raw10474step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10474step2 raw10474step1; decide +kernel
      have hl : raw10474step2Labels = raw10474step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10474step1 raw10474step1Labels permutation9 permutation3
    mixedMoment B raw10474step2 raw10474step2Labels = mixedMoment B raw10474step3 raw10474step3Labels := by
      have ha : raw10474step3 = raw10474step2 := by apply Matrix.ext; unfold raw10474step3 raw10474step2; decide +kernel
      have hl : raw10474step2Labels = labelEmbedding6 ∘ raw10474step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10474step2 raw10474step2Labels raw10474step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw10475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10475step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10475step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10475 raw10475Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw10475 raw10475Labels = mixedMoment B raw10475step0 raw10475step0Labels := by
      have hz : ∀ j, raw10475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10475step0 = (fun i j => raw10475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10475step0 raw10475; decide +kernel
      have hl : raw10475step0Labels = raw10475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10475 raw10475Labels permutation346 hz
    mixedMoment B raw10475step0 raw10475step0Labels = mixedMoment B raw10475step1 raw10475step1Labels := by
      have hz : ∀ j, raw10475step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10475step1 = (fun i j => raw10475step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10475step1 raw10475step0; decide +kernel
      have hl : raw10475step1Labels = raw10475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10475step0 raw10475step0Labels permutation56 hz
    mixedMoment B raw10475step1 raw10475step1Labels = mixedMoment B raw10475step2 raw10475step2Labels := by
      have ha : raw10475step2 = (fun i j => raw10475step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10475step2 raw10475step1; decide +kernel
      have hl : raw10475step2Labels = raw10475step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10475step1 raw10475step1Labels permutation8 permutation3
    mixedMoment B raw10475step2 raw10475step2Labels = mixedMoment B raw10475step3 raw10475step3Labels := by
      have ha : raw10475step3 = raw10475step2 := by apply Matrix.ext; unfold raw10475step3 raw10475step2; decide +kernel
      have hl : raw10475step2Labels = labelEmbedding6 ∘ raw10475step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10475step2 raw10475step2Labels raw10475step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw10476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10476step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10476step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10476step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10476step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10476 raw10476Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw10476 raw10476Labels = mixedMoment B raw10476step0 raw10476step0Labels := by
      have hz : ∀ j, raw10476 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10476step0 = (fun i j => raw10476 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10476step0 raw10476; decide +kernel
      have hl : raw10476step0Labels = raw10476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10476 raw10476Labels permutation346 hz
    mixedMoment B raw10476step0 raw10476step0Labels = mixedMoment B raw10476step1 raw10476step1Labels := by
      have ha : raw10476step1 = (fun i j => raw10476step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10476step1 raw10476step0; decide +kernel
      have hl : raw10476step1Labels = raw10476step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10476step0 raw10476step0Labels permutation151 permutation3
    mixedMoment B raw10476step1 raw10476step1Labels = mixedMoment B raw10476step2 raw10476step2Labels := by
      have ha : raw10476step2 = -raw10476step1 := by apply Matrix.ext; change ∀ i j, raw10476step2 i j = -(raw10476step1 i j); unfold raw10476step2 raw10476step1; decide +kernel
      have hl : raw10476step2Labels = raw10476step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10476step2 raw10476step2Labels = mixedMoment B raw10476step3 raw10476step3Labels := by
      have ha : raw10476step3 = raw10476step2 := by apply Matrix.ext; unfold raw10476step3 raw10476step2; decide +kernel
      have hl : raw10476step2Labels = labelEmbedding6 ∘ raw10476step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10476step2 raw10476step2Labels raw10476step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw10477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10477step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10477step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10477step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10477step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10477 raw10477Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw10477 raw10477Labels = mixedMoment B raw10477step0 raw10477step0Labels := by
      have hz : ∀ j, raw10477 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10477step0 = (fun i j => raw10477 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10477step0 raw10477; decide +kernel
      have hl : raw10477step0Labels = raw10477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10477 raw10477Labels permutation265 hz
    mixedMoment B raw10477step0 raw10477step0Labels = mixedMoment B raw10477step1 raw10477step1Labels := by
      have ha : raw10477step1 = (fun i j => raw10477step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10477step1 raw10477step0; decide +kernel
      have hl : raw10477step1Labels = raw10477step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10477step0 raw10477step0Labels permutation151 permutation3
    mixedMoment B raw10477step1 raw10477step1Labels = mixedMoment B raw10477step2 raw10477step2Labels := by
      have ha : raw10477step2 = -raw10477step1 := by apply Matrix.ext; change ∀ i j, raw10477step2 i j = -(raw10477step1 i j); unfold raw10477step2 raw10477step1; decide +kernel
      have hl : raw10477step2Labels = raw10477step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10477step2 raw10477step2Labels = mixedMoment B raw10477step3 raw10477step3Labels := by
      have ha : raw10477step3 = raw10477step2 := by apply Matrix.ext; unfold raw10477step3 raw10477step2; decide +kernel
      have hl : raw10477step2Labels = labelEmbedding6 ∘ raw10477step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10477step2 raw10477step2Labels raw10477step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw10478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw10478step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw10478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10478 raw10478Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw10478 raw10478Labels = mixedMoment B raw10478step0 raw10478step0Labels := by
      have hz : ∀ j, raw10478 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10478step0 = (fun i j => raw10478 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10478step0 raw10478; decide +kernel
      have hl : raw10478step0Labels = raw10478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10478 raw10478Labels permutation346 hz
    mixedMoment B raw10478step0 raw10478step0Labels = mixedMoment B raw10478step1 raw10478step1Labels := by
      have hz : ∀ j, raw10478step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10478step1 = (fun i j => raw10478step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10478step1 raw10478step0; decide +kernel
      have hl : raw10478step1Labels = raw10478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10478step0 raw10478step0Labels permutation56 hz
    mixedMoment B raw10478step1 raw10478step1Labels = mixedMoment B raw10478step2 raw10478step2Labels := by
      have ha : raw10478step2 = (fun i j => raw10478step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10478step2 raw10478step1; decide +kernel
      have hl : raw10478step2Labels = raw10478step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10478step1 raw10478step1Labels permutation8 permutation3
    mixedMoment B raw10478step2 raw10478step2Labels = mixedMoment B raw10478step3 raw10478step3Labels := by
      have ha : raw10478step3 = raw10478step2 := by apply Matrix.ext; unfold raw10478step3 raw10478step2; decide +kernel
      have hl : raw10478step2Labels = labelEmbedding6 ∘ raw10478step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10478step2 raw10478step2Labels raw10478step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

def raw10479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10479step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10479step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10479step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10479 raw10479Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw10479 raw10479Labels = mixedMoment B raw10479step0 raw10479step0Labels := by
      have hz : ∀ j, raw10479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10479step0 = (fun i j => raw10479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10479step0 raw10479; decide +kernel
      have hl : raw10479step0Labels = raw10479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10479 raw10479Labels permutation346 hz
    mixedMoment B raw10479step0 raw10479step0Labels = mixedMoment B raw10479step1 raw10479step1Labels := by
      have hz : ∀ j, raw10479step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10479step1 = (fun i j => raw10479step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10479step1 raw10479step0; decide +kernel
      have hl : raw10479step1Labels = raw10479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10479step0 raw10479step0Labels permutation56 hz
    mixedMoment B raw10479step1 raw10479step1Labels = mixedMoment B raw10479step2 raw10479step2Labels := by
      have ha : raw10479step2 = (fun i j => raw10479step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10479step2 raw10479step1; decide +kernel
      have hl : raw10479step2Labels = raw10479step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10479step1 raw10479step1Labels permutation8 permutation3
    mixedMoment B raw10479step2 raw10479step2Labels = mixedMoment B raw10479step3 raw10479step3Labels := by
      have ha : raw10479step3 = raw10479step2 := by apply Matrix.ext; unfold raw10479step3 raw10479step2; decide +kernel
      have hl : raw10479step2Labels = labelEmbedding6 ∘ raw10479step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10479step2 raw10479step2Labels raw10479step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw10480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10480 raw10480Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw10480 raw10480Labels = mixedMoment B raw10480step0 raw10480step0Labels := by
      have hz : ∀ j, raw10480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10480step0 = (fun i j => raw10480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10480step0 raw10480; decide +kernel
      have hl : raw10480step0Labels = raw10480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10480 raw10480Labels permutation346 hz
    mixedMoment B raw10480step0 raw10480step0Labels = mixedMoment B raw10480step1 raw10480step1Labels := by
      have ha : raw10480step1 = (fun i j => raw10480step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10480step1 raw10480step0; decide +kernel
      have hl : raw10480step1Labels = raw10480step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10480step0 raw10480step0Labels permutation151 permutation3
    mixedMoment B raw10480step1 raw10480step1Labels = mixedMoment B raw10480step2 raw10480step2Labels := by
      have ha : raw10480step2 = -raw10480step1 := by apply Matrix.ext; change ∀ i j, raw10480step2 i j = -(raw10480step1 i j); unfold raw10480step2 raw10480step1; decide +kernel
      have hl : raw10480step2Labels = raw10480step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw10481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10481 raw10481Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw10481 raw10481Labels = mixedMoment B raw10481step0 raw10481step0Labels := by
      have hz : ∀ j, raw10481 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10481step0 = (fun i j => raw10481 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10481step0 raw10481; decide +kernel
      have hl : raw10481step0Labels = raw10481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10481 raw10481Labels permutation265 hz
    mixedMoment B raw10481step0 raw10481step0Labels = mixedMoment B raw10481step1 raw10481step1Labels := by
      have ha : raw10481step1 = (fun i j => raw10481step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10481step1 raw10481step0; decide +kernel
      have hl : raw10481step1Labels = raw10481step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10481step0 raw10481step0Labels permutation151 permutation3
    mixedMoment B raw10481step1 raw10481step1Labels = mixedMoment B raw10481step2 raw10481step2Labels := by
      have ha : raw10481step2 = -raw10481step1 := by apply Matrix.ext; change ∀ i j, raw10481step2 i j = -(raw10481step1 i j); unfold raw10481step2 raw10481step1; decide +kernel
      have hl : raw10481step2Labels = raw10481step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw10482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10482step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw10482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10482 raw10482Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw10482 raw10482Labels = mixedMoment B raw10482step0 raw10482step0Labels := by
      have hz : ∀ j, raw10482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10482step0 = (fun i j => raw10482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10482step0 raw10482; decide +kernel
      have hl : raw10482step0Labels = raw10482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10482 raw10482Labels permutation346 hz
    mixedMoment B raw10482step0 raw10482step0Labels = mixedMoment B raw10482step1 raw10482step1Labels := by
      have hz : ∀ j, raw10482step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10482step1 = (fun i j => raw10482step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10482step1 raw10482step0; decide +kernel
      have hl : raw10482step1Labels = raw10482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10482step0 raw10482step0Labels permutation56 hz
    mixedMoment B raw10482step1 raw10482step1Labels = mixedMoment B raw10482step2 raw10482step2Labels := by
      have ha : raw10482step2 = (fun i j => raw10482step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10482step2 raw10482step1; decide +kernel
      have hl : raw10482step2Labels = raw10482step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10482step1 raw10482step1Labels permutation8 permutation3
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw10483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw10483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10483 raw10483Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw10483 raw10483Labels = mixedMoment B raw10483step0 raw10483step0Labels := by
      have hz : ∀ j, raw10483 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10483step0 = (fun i j => raw10483 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10483step0 raw10483; decide +kernel
      have hl : raw10483step0Labels = raw10483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10483 raw10483Labels permutation346 hz
    mixedMoment B raw10483step0 raw10483step0Labels = mixedMoment B raw10483step1 raw10483step1Labels := by
      have hz : ∀ j, raw10483step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10483step1 = (fun i j => raw10483step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10483step1 raw10483step0; decide +kernel
      have hl : raw10483step1Labels = raw10483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10483step0 raw10483step0Labels permutation56 hz
    mixedMoment B raw10483step1 raw10483step1Labels = mixedMoment B raw10483step2 raw10483step2Labels := by
      have ha : raw10483step2 = (fun i j => raw10483step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10483step2 raw10483step1; decide +kernel
      have hl : raw10483step2Labels = raw10483step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10483step1 raw10483step1Labels permutation8 permutation3
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw10484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10484 raw10484Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw10484 raw10484Labels = mixedMoment B raw10484step0 raw10484step0Labels := by
      have hz : ∀ j, raw10484 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10484step0 = (fun i j => raw10484 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10484step0 raw10484; decide +kernel
      have hl : raw10484step0Labels = raw10484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10484 raw10484Labels permutation346 hz
    mixedMoment B raw10484step0 raw10484step0Labels = mixedMoment B raw10484step1 raw10484step1Labels := by
      have hz : ∀ j, raw10484step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10484step1 = (fun i j => raw10484step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10484step1 raw10484step0; decide +kernel
      have hl : raw10484step1Labels = raw10484step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10484step0 raw10484step0Labels permutation56 hz
    mixedMoment B raw10484step1 raw10484step1Labels = mixedMoment B raw10484step2 raw10484step2Labels := by
      have ha : raw10484step2 = (fun i j => raw10484step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10484step2 raw10484step1; decide +kernel
      have hl : raw10484step2Labels = raw10484step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10484step1 raw10484step1Labels permutation9 permutation3
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw10485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10485 raw10485Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw10485 raw10485Labels = mixedMoment B raw10485step0 raw10485step0Labels := by
      have hz : ∀ j, raw10485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10485step0 = (fun i j => raw10485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10485step0 raw10485; decide +kernel
      have hl : raw10485step0Labels = raw10485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10485 raw10485Labels permutation346 hz
    mixedMoment B raw10485step0 raw10485step0Labels = mixedMoment B raw10485step1 raw10485step1Labels := by
      have ha : raw10485step1 = (fun i j => raw10485step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10485step1 raw10485step0; decide +kernel
      have hl : raw10485step1Labels = raw10485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10485step0 raw10485step0Labels permutation38 permutation3
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw10486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10486 raw10486Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw10486 raw10486Labels = mixedMoment B raw10486step0 raw10486step0Labels := by
      have ha : raw10486step0 = (fun i j => raw10486 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10486step0 raw10486; decide +kernel
      have hl : raw10486step0Labels = raw10486Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10486 raw10486Labels permutation182 permutation3
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw10487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10487 raw10487Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw10487 raw10487Labels = mixedMoment B raw10487step0 raw10487step0Labels := by
      have hz : ∀ j, raw10487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10487step0 = (fun i j => raw10487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10487step0 raw10487; decide +kernel
      have hl : raw10487step0Labels = raw10487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10487 raw10487Labels permutation346 hz
    mixedMoment B raw10487step0 raw10487step0Labels = mixedMoment B raw10487step1 raw10487step1Labels := by
      have ha : raw10487step1 = (fun i j => raw10487step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10487step1 raw10487step0; decide +kernel
      have hl : raw10487step1Labels = raw10487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10487step0 raw10487step0Labels permutation38 permutation3
    _ = mixedMoment B node2404 node2404Labels := by rfl

def raw10488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10488 raw10488Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw10488 raw10488Labels = mixedMoment B raw10488step0 raw10488step0Labels := by
      have hz : ∀ j, raw10488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10488step0 = (fun i j => raw10488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10488step0 raw10488; decide +kernel
      have hl : raw10488step0Labels = raw10488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10488 raw10488Labels permutation346 hz
    mixedMoment B raw10488step0 raw10488step0Labels = mixedMoment B raw10488step1 raw10488step1Labels := by
      have ha : raw10488step1 = (fun i j => raw10488step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10488step1 raw10488step0; decide +kernel
      have hl : raw10488step1Labels = raw10488step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10488step0 raw10488step0Labels permutation40 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw10489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10489 raw10489Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw10489 raw10489Labels = mixedMoment B raw10489step0 raw10489step0Labels := by
      have hz : ∀ j, raw10489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10489step0 = (fun i j => raw10489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10489step0 raw10489; decide +kernel
      have hl : raw10489step0Labels = raw10489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10489 raw10489Labels permutation346 hz
    mixedMoment B raw10489step0 raw10489step0Labels = mixedMoment B raw10489step1 raw10489step1Labels := by
      have ha : raw10489step1 = (fun i j => raw10489step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10489step1 raw10489step0; decide +kernel
      have hl : raw10489step1Labels = raw10489step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10489step0 raw10489step0Labels permutation42 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw10490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10490 raw10490Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw10490 raw10490Labels = mixedMoment B raw10490step0 raw10490step0Labels := by
      have hz : ∀ j, raw10490 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10490step0 = (fun i j => raw10490 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10490step0 raw10490; decide +kernel
      have hl : raw10490step0Labels = raw10490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10490 raw10490Labels permutation265 hz
    mixedMoment B raw10490step0 raw10490step0Labels = mixedMoment B raw10490step1 raw10490step1Labels := by
      have ha : raw10490step1 = (fun i j => raw10490step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10490step1 raw10490step0; decide +kernel
      have hl : raw10490step1Labels = raw10490step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10490step0 raw10490step0Labels permutation38 permutation3
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw10491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10491 raw10491Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw10491 raw10491Labels = mixedMoment B raw10491step0 raw10491step0Labels := by
      have ha : raw10491step0 = (fun i j => raw10491 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10491step0 raw10491; decide +kernel
      have hl : raw10491step0Labels = raw10491Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10491 raw10491Labels permutation158 permutation3
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw10492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10492 raw10492Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw10492 raw10492Labels = mixedMoment B raw10492step0 raw10492step0Labels := by
      have hz : ∀ j, raw10492 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10492step0 = (fun i j => raw10492 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10492step0 raw10492; decide +kernel
      have hl : raw10492step0Labels = raw10492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10492 raw10492Labels permutation265 hz
    mixedMoment B raw10492step0 raw10492step0Labels = mixedMoment B raw10492step1 raw10492step1Labels := by
      have ha : raw10492step1 = (fun i j => raw10492step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10492step1 raw10492step0; decide +kernel
      have hl : raw10492step1Labels = raw10492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10492step0 raw10492step0Labels permutation38 permutation3
    _ = mixedMoment B node2404 node2404Labels := by rfl

def raw10493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10493 raw10493Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw10493 raw10493Labels = mixedMoment B raw10493step0 raw10493step0Labels := by
      have hz : ∀ j, raw10493 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10493step0 = (fun i j => raw10493 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10493step0 raw10493; decide +kernel
      have hl : raw10493step0Labels = raw10493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10493 raw10493Labels permutation265 hz
    mixedMoment B raw10493step0 raw10493step0Labels = mixedMoment B raw10493step1 raw10493step1Labels := by
      have ha : raw10493step1 = (fun i j => raw10493step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10493step1 raw10493step0; decide +kernel
      have hl : raw10493step1Labels = raw10493step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10493step0 raw10493step0Labels permutation40 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw10494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10494 raw10494Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw10494 raw10494Labels = mixedMoment B raw10494step0 raw10494step0Labels := by
      have hz : ∀ j, raw10494 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10494step0 = (fun i j => raw10494 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10494step0 raw10494; decide +kernel
      have hl : raw10494step0Labels = raw10494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10494 raw10494Labels permutation265 hz
    mixedMoment B raw10494step0 raw10494step0Labels = mixedMoment B raw10494step1 raw10494step1Labels := by
      have ha : raw10494step1 = (fun i j => raw10494step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10494step1 raw10494step0; decide +kernel
      have hl : raw10494step1Labels = raw10494step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10494step0 raw10494step0Labels permutation42 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw10495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10495step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10495 raw10495Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw10495 raw10495Labels = mixedMoment B raw10495step0 raw10495step0Labels := by
      have hz : ∀ j, raw10495 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10495step0 = (fun i j => raw10495 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10495step0 raw10495; decide +kernel
      have hl : raw10495step0Labels = raw10495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10495 raw10495Labels permutation346 hz
    mixedMoment B raw10495step0 raw10495step0Labels = mixedMoment B raw10495step1 raw10495step1Labels := by
      have hz : ∀ j, raw10495step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10495step1 = (fun i j => raw10495step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10495step1 raw10495step0; decide +kernel
      have hl : raw10495step1Labels = raw10495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10495step0 raw10495step0Labels permutation56 hz
    mixedMoment B raw10495step1 raw10495step1Labels = mixedMoment B raw10495step2 raw10495step2Labels := by
      have ha : raw10495step2 = (fun i j => raw10495step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10495step2 raw10495step1; decide +kernel
      have hl : raw10495step2Labels = raw10495step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10495step1 raw10495step1Labels permutation8 permutation3
    _ = mixedMoment B node1083 node1083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
