import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8576 raw8576Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw8576 raw8576Labels = mixedMoment B raw8576step0 raw8576step0Labels := by
      have hz : ∀ j, raw8576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8576step0 = (fun i j => raw8576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8576step0 raw8576; decide +kernel
      have hl : raw8576step0Labels = raw8576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8576 raw8576Labels permutation346 hz
    mixedMoment B raw8576step0 raw8576step0Labels = mixedMoment B raw8576step1 raw8576step1Labels := by
      have ha : raw8576step1 = (fun i j => raw8576step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8576step1 raw8576step0; decide +kernel
      have hl : raw8576step1Labels = raw8576step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8576step0 raw8576step0Labels permutation32 permutation6
    _ = mixedMoment B node2758 node2758Labels := by rfl

def raw8577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8577 raw8577Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw8577 raw8577Labels = mixedMoment B raw8577step0 raw8577step0Labels := by
      have hz : ∀ j, raw8577 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8577step0 = (fun i j => raw8577 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8577step0 raw8577; decide +kernel
      have hl : raw8577step0Labels = raw8577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8577 raw8577Labels permutation265 hz
    mixedMoment B raw8577step0 raw8577step0Labels = mixedMoment B raw8577step1 raw8577step1Labels := by
      have ha : raw8577step1 = (fun i j => raw8577step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8577step1 raw8577step0; decide +kernel
      have hl : raw8577step1Labels = raw8577step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8577step0 raw8577step0Labels permutation32 permutation6
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw8578 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8578 raw8578Labels = mixedMoment B node2629 node2629Labels := by
  calc
    mixedMoment B raw8578 raw8578Labels = mixedMoment B raw8578step0 raw8578step0Labels := by
      have hz : ∀ j, raw8578 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8578step0 = (fun i j => raw8578 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8578step0 raw8578; decide +kernel
      have hl : raw8578step0Labels = raw8578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8578 raw8578Labels permutation265 hz
    mixedMoment B raw8578step0 raw8578step0Labels = mixedMoment B raw8578step1 raw8578step1Labels := by
      have ha : raw8578step1 = (fun i j => raw8578step0 (permutation122 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8578step1 raw8578step0; decide +kernel
      have hl : raw8578step1Labels = raw8578step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8578step0 raw8578step0Labels permutation122 permutation3
    _ = mixedMoment B node2629 node2629Labels := by rfl

def raw8579 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8579 raw8579Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw8579 raw8579Labels = mixedMoment B raw8579step0 raw8579step0Labels := by
      have hz : ∀ j, raw8579 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8579step0 = (fun i j => raw8579 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8579step0 raw8579; decide +kernel
      have hl : raw8579step0Labels = raw8579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8579 raw8579Labels permutation265 hz
    mixedMoment B raw8579step0 raw8579step0Labels = mixedMoment B raw8579step1 raw8579step1Labels := by
      have ha : raw8579step1 = (fun i j => raw8579step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8579step1 raw8579step0; decide +kernel
      have hl : raw8579step1Labels = raw8579step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8579step0 raw8579step0Labels permutation32 permutation6
    _ = mixedMoment B node2758 node2758Labels := by rfl

def raw8580 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8580step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 2, -1], ![-2, 1, 1]]
def raw8580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8580step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw8580step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8580 raw8580Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw8580 raw8580Labels = mixedMoment B raw8580step0 raw8580step0Labels := by
      have hz : ∀ j, raw8580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8580step0 = (fun i j => raw8580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8580step0 raw8580; decide +kernel
      have hl : raw8580step0Labels = raw8580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8580 raw8580Labels permutation346 hz
    mixedMoment B raw8580step0 raw8580step0Labels = mixedMoment B raw8580step1 raw8580step1Labels := by
      have hz : ∀ j, raw8580step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8580step1 = (fun i j => raw8580step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8580step1 raw8580step0; decide +kernel
      have hl : raw8580step1Labels = raw8580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8580step0 raw8580step0Labels permutation56 hz
    mixedMoment B raw8580step1 raw8580step1Labels = mixedMoment B raw8580step2 raw8580step2Labels := by
      have ha : raw8580step2 = (fun i j => raw8580step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8580step2 raw8580step1; decide +kernel
      have hl : raw8580step2Labels = raw8580step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8580step1 raw8580step1Labels permutation15 permutation3
    mixedMoment B raw8580step2 raw8580step2Labels = mixedMoment B raw8580step3 raw8580step3Labels := by
      have ha : raw8580step3 = -raw8580step2 := by apply Matrix.ext; change ∀ i j, raw8580step3 i j = -(raw8580step2 i j); unfold raw8580step3 raw8580step2; decide +kernel
      have hl : raw8580step3Labels = raw8580step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2282 node2282Labels := by rfl

def raw8581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8581 raw8581Labels = mixedMoment B node2129 node2129Labels := by
  calc
    mixedMoment B raw8581 raw8581Labels = mixedMoment B raw8581step0 raw8581step0Labels := by
      have hz : ∀ j, raw8581 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8581step0 = (fun i j => raw8581 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8581step0 raw8581; decide +kernel
      have hl : raw8581step0Labels = raw8581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8581 raw8581Labels permutation265 hz
    mixedMoment B raw8581step0 raw8581step0Labels = mixedMoment B raw8581step1 raw8581step1Labels := by
      have ha : raw8581step1 = (fun i j => raw8581step0 (permutation84 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8581step1 raw8581step0; decide +kernel
      have hl : raw8581step1Labels = raw8581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8581step0 raw8581step0Labels permutation84 permutation3
    mixedMoment B raw8581step1 raw8581step1Labels = mixedMoment B raw8581step2 raw8581step2Labels := by
      have ha : raw8581step2 = -raw8581step1 := by apply Matrix.ext; change ∀ i j, raw8581step2 i j = -(raw8581step1 i j); unfold raw8581step2 raw8581step1; decide +kernel
      have hl : raw8581step2Labels = raw8581step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2129 node2129Labels := by rfl

def raw8582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8582step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw8582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8582step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8582 raw8582Labels = mixedMoment B node2130 node2130Labels := by
  calc
    mixedMoment B raw8582 raw8582Labels = mixedMoment B raw8582step0 raw8582step0Labels := by
      have hz : ∀ j, raw8582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8582step0 = (fun i j => raw8582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8582step0 raw8582; decide +kernel
      have hl : raw8582step0Labels = raw8582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8582 raw8582Labels permutation346 hz
    mixedMoment B raw8582step0 raw8582step0Labels = mixedMoment B raw8582step1 raw8582step1Labels := by
      have hz : ∀ j, raw8582step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8582step1 = (fun i j => raw8582step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8582step1 raw8582step0; decide +kernel
      have hl : raw8582step1Labels = raw8582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8582step0 raw8582step0Labels permutation56 hz
    mixedMoment B raw8582step1 raw8582step1Labels = mixedMoment B raw8582step2 raw8582step2Labels := by
      have ha : raw8582step2 = (fun i j => raw8582step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8582step2 raw8582step1; decide +kernel
      have hl : raw8582step2Labels = raw8582step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8582step1 raw8582step1Labels permutation15 permutation3
    mixedMoment B raw8582step2 raw8582step2Labels = mixedMoment B raw8582step3 raw8582step3Labels := by
      have ha : raw8582step3 = -raw8582step2 := by apply Matrix.ext; change ∀ i j, raw8582step3 i j = -(raw8582step2 i j); unfold raw8582step3 raw8582step2; decide +kernel
      have hl : raw8582step3Labels = raw8582step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2130 node2130Labels := by rfl

def raw8583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8583step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw8583step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8583step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8583 raw8583Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw8583 raw8583Labels = mixedMoment B raw8583step0 raw8583step0Labels := by
      have hz : ∀ j, raw8583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8583step0 = (fun i j => raw8583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8583step0 raw8583; decide +kernel
      have hl : raw8583step0Labels = raw8583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8583 raw8583Labels permutation346 hz
    mixedMoment B raw8583step0 raw8583step0Labels = mixedMoment B raw8583step1 raw8583step1Labels := by
      have hz : ∀ j, raw8583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8583step1 = (fun i j => raw8583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8583step1 raw8583step0; decide +kernel
      have hl : raw8583step1Labels = raw8583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8583step0 raw8583step0Labels permutation56 hz
    mixedMoment B raw8583step1 raw8583step1Labels = mixedMoment B raw8583step2 raw8583step2Labels := by
      have ha : raw8583step2 = (fun i j => raw8583step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8583step2 raw8583step1; decide +kernel
      have hl : raw8583step2Labels = raw8583step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8583step1 raw8583step1Labels permutation15 permutation3
    mixedMoment B raw8583step2 raw8583step2Labels = mixedMoment B raw8583step3 raw8583step3Labels := by
      have ha : raw8583step3 = -raw8583step2 := by apply Matrix.ext; change ∀ i j, raw8583step3 i j = -(raw8583step2 i j); unfold raw8583step3 raw8583step2; decide +kernel
      have hl : raw8583step3Labels = raw8583step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2138 node2138Labels := by rfl

def raw8584 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8584step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw8584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8584 raw8584Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw8584 raw8584Labels = mixedMoment B raw8584step0 raw8584step0Labels := by
      have hz : ∀ j, raw8584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8584step0 = (fun i j => raw8584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8584step0 raw8584; decide +kernel
      have hl : raw8584step0Labels = raw8584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8584 raw8584Labels permutation346 hz
    mixedMoment B raw8584step0 raw8584step0Labels = mixedMoment B raw8584step1 raw8584step1Labels := by
      have hz : ∀ j, raw8584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8584step1 = (fun i j => raw8584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8584step1 raw8584step0; decide +kernel
      have hl : raw8584step1Labels = raw8584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8584step0 raw8584step0Labels permutation56 hz
    mixedMoment B raw8584step1 raw8584step1Labels = mixedMoment B raw8584step2 raw8584step2Labels := by
      have ha : raw8584step2 = (fun i j => raw8584step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8584step2 raw8584step1; decide +kernel
      have hl : raw8584step2Labels = raw8584step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8584step1 raw8584step1Labels permutation8 permutation6
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw8585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw8585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8585 raw8585Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw8585 raw8585Labels = mixedMoment B raw8585step0 raw8585step0Labels := by
      have hz : ∀ j, raw8585 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8585step0 = (fun i j => raw8585 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8585step0 raw8585; decide +kernel
      have hl : raw8585step0Labels = raw8585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8585 raw8585Labels permutation265 hz
    mixedMoment B raw8585step0 raw8585step0Labels = mixedMoment B raw8585step1 raw8585step1Labels := by
      have ha : raw8585step1 = (fun i j => raw8585step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8585step1 raw8585step0; decide +kernel
      have hl : raw8585step1Labels = raw8585step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8585step0 raw8585step0Labels permutation32 permutation6
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw8586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw8586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8586 raw8586Labels = mixedMoment B node2771 node2771Labels := by
  calc
    mixedMoment B raw8586 raw8586Labels = mixedMoment B raw8586step0 raw8586step0Labels := by
      have hz : ∀ j, raw8586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8586step0 = (fun i j => raw8586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8586step0 raw8586; decide +kernel
      have hl : raw8586step0Labels = raw8586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8586 raw8586Labels permutation346 hz
    mixedMoment B raw8586step0 raw8586step0Labels = mixedMoment B raw8586step1 raw8586step1Labels := by
      have hz : ∀ j, raw8586step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8586step1 = (fun i j => raw8586step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8586step1 raw8586step0; decide +kernel
      have hl : raw8586step1Labels = raw8586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8586step0 raw8586step0Labels permutation56 hz
    mixedMoment B raw8586step1 raw8586step1Labels = mixedMoment B raw8586step2 raw8586step2Labels := by
      have ha : raw8586step2 = (fun i j => raw8586step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8586step2 raw8586step1; decide +kernel
      have hl : raw8586step2Labels = raw8586step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8586step1 raw8586step1Labels permutation24 permutation3
    _ = mixedMoment B node2771 node2771Labels := by rfl

def raw8587 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8587Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8587step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8587step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8587 raw8587Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw8587 raw8587Labels = mixedMoment B raw8587step0 raw8587step0Labels := by
      have hz : ∀ j, raw8587 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8587step0 = (fun i j => raw8587 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8587step0 raw8587; decide +kernel
      have hl : raw8587step0Labels = raw8587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8587 raw8587Labels permutation265 hz
    mixedMoment B raw8587step0 raw8587step0Labels = mixedMoment B raw8587step1 raw8587step1Labels := by
      have ha : raw8587step1 = (fun i j => raw8587step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8587step1 raw8587step0; decide +kernel
      have hl : raw8587step1Labels = raw8587step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8587step0 raw8587step0Labels permutation38 permutation7
    mixedMoment B raw8587step1 raw8587step1Labels = mixedMoment B raw8587step2 raw8587step2Labels := by
      have ha : raw8587step2 = raw8587step1 := by apply Matrix.ext; unfold raw8587step2 raw8587step1; decide +kernel
      have hl : raw8587step1Labels = labelEmbedding1 ∘ raw8587step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8587step1 raw8587step1Labels raw8587step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw8588 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8588Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8588step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8588step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw8588step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw8588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8588 raw8588Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw8588 raw8588Labels = mixedMoment B raw8588step0 raw8588step0Labels := by
      have hz : ∀ j, raw8588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8588step0 = (fun i j => raw8588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8588step0 raw8588; decide +kernel
      have hl : raw8588step0Labels = raw8588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8588 raw8588Labels permutation346 hz
    mixedMoment B raw8588step0 raw8588step0Labels = mixedMoment B raw8588step1 raw8588step1Labels := by
      have hz : ∀ j, raw8588step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8588step1 = (fun i j => raw8588step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8588step1 raw8588step0; decide +kernel
      have hl : raw8588step1Labels = raw8588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8588step0 raw8588step0Labels permutation56 hz
    mixedMoment B raw8588step1 raw8588step1Labels = mixedMoment B raw8588step2 raw8588step2Labels := by
      have ha : raw8588step2 = (fun i j => raw8588step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8588step2 raw8588step1; decide +kernel
      have hl : raw8588step2Labels = raw8588step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8588step1 raw8588step1Labels permutation8 permutation7
    mixedMoment B raw8588step2 raw8588step2Labels = mixedMoment B raw8588step3 raw8588step3Labels := by
      have ha : raw8588step3 = raw8588step2 := by apply Matrix.ext; unfold raw8588step3 raw8588step2; decide +kernel
      have hl : raw8588step2Labels = labelEmbedding1 ∘ raw8588step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8588step2 raw8588step2Labels raw8588step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw8589 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8589Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8589step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8589step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8589step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8589step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8589step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8589 raw8589Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw8589 raw8589Labels = mixedMoment B raw8589step0 raw8589step0Labels := by
      have hz : ∀ j, raw8589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8589step0 = (fun i j => raw8589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8589step0 raw8589; decide +kernel
      have hl : raw8589step0Labels = raw8589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8589 raw8589Labels permutation346 hz
    mixedMoment B raw8589step0 raw8589step0Labels = mixedMoment B raw8589step1 raw8589step1Labels := by
      have hz : ∀ j, raw8589step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8589step1 = (fun i j => raw8589step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8589step1 raw8589step0; decide +kernel
      have hl : raw8589step1Labels = raw8589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8589step0 raw8589step0Labels permutation56 hz
    mixedMoment B raw8589step1 raw8589step1Labels = mixedMoment B raw8589step2 raw8589step2Labels := by
      have ha : raw8589step2 = (fun i j => raw8589step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8589step2 raw8589step1; decide +kernel
      have hl : raw8589step2Labels = raw8589step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8589step1 raw8589step1Labels permutation8 permutation7
    mixedMoment B raw8589step2 raw8589step2Labels = mixedMoment B raw8589step3 raw8589step3Labels := by
      have ha : raw8589step3 = raw8589step2 := by apply Matrix.ext; unfold raw8589step3 raw8589step2; decide +kernel
      have hl : raw8589step2Labels = labelEmbedding1 ∘ raw8589step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8589step2 raw8589step2Labels raw8589step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw8590 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8590Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8590step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw8590step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw8590step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8590step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw8590step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8590 raw8590Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw8590 raw8590Labels = mixedMoment B raw8590step0 raw8590step0Labels := by
      have hz : ∀ j, raw8590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8590step0 = (fun i j => raw8590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8590step0 raw8590; decide +kernel
      have hl : raw8590step0Labels = raw8590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8590 raw8590Labels permutation346 hz
    mixedMoment B raw8590step0 raw8590step0Labels = mixedMoment B raw8590step1 raw8590step1Labels := by
      have ha : raw8590step1 = (fun i j => raw8590step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8590step1 raw8590step0; decide +kernel
      have hl : raw8590step1Labels = raw8590step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8590step0 raw8590step0Labels permutation48 permutation5
    mixedMoment B raw8590step1 raw8590step1Labels = mixedMoment B raw8590step2 raw8590step2Labels := by
      have ha : raw8590step2 = -raw8590step1 := by apply Matrix.ext; change ∀ i j, raw8590step2 i j = -(raw8590step1 i j); unfold raw8590step2 raw8590step1; decide +kernel
      have hl : raw8590step2Labels = raw8590step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8590step2 raw8590step2Labels = mixedMoment B raw8590step3 raw8590step3Labels := by
      have ha : raw8590step3 = raw8590step2 := by apply Matrix.ext; unfold raw8590step3 raw8590step2; decide +kernel
      have hl : raw8590step2Labels = labelEmbedding1 ∘ raw8590step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8590step2 raw8590step2Labels raw8590step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw8591 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8591step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8591 raw8591Labels = mixedMoment B node3017 node3017Labels := by
  calc
    mixedMoment B raw8591 raw8591Labels = mixedMoment B raw8591step0 raw8591step0Labels := by
      have ha : raw8591step0 = (fun i j => raw8591 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8591step0 raw8591; decide +kernel
      have hl : raw8591step0Labels = raw8591Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8591 raw8591Labels permutation200 permutation7
    mixedMoment B raw8591step0 raw8591step0Labels = mixedMoment B raw8591step1 raw8591step1Labels := by
      have ha : raw8591step1 = raw8591step0 := by apply Matrix.ext; unfold raw8591step1 raw8591step0; decide +kernel
      have hl : raw8591step0Labels = labelEmbedding1 ∘ raw8591step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8591step0 raw8591step0Labels raw8591step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3017 node3017Labels := by rfl

def raw8592 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8592 raw8592Labels = mixedMoment B node3026 node3026Labels := by
  calc
    mixedMoment B raw8592 raw8592Labels = mixedMoment B raw8592step0 raw8592step0Labels := by
      have hz : ∀ j, raw8592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8592step0 = (fun i j => raw8592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8592step0 raw8592; decide +kernel
      have hl : raw8592step0Labels = raw8592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8592 raw8592Labels permutation346 hz
    mixedMoment B raw8592step0 raw8592step0Labels = mixedMoment B raw8592step1 raw8592step1Labels := by
      have ha : raw8592step1 = (fun i j => raw8592step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8592step1 raw8592step0; decide +kernel
      have hl : raw8592step1Labels = raw8592step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8592step0 raw8592step0Labels permutation38 permutation7
    mixedMoment B raw8592step1 raw8592step1Labels = mixedMoment B raw8592step2 raw8592step2Labels := by
      have ha : raw8592step2 = raw8592step1 := by apply Matrix.ext; unfold raw8592step2 raw8592step1; decide +kernel
      have hl : raw8592step1Labels = labelEmbedding1 ∘ raw8592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8592step1 raw8592step1Labels raw8592step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3026 node3026Labels := by rfl

def raw8593 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw8593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw8593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8593 raw8593Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw8593 raw8593Labels = mixedMoment B raw8593step0 raw8593step0Labels := by
      have hz : ∀ j, raw8593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8593step0 = (fun i j => raw8593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8593step0 raw8593; decide +kernel
      have hl : raw8593step0Labels = raw8593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8593 raw8593Labels permutation346 hz
    mixedMoment B raw8593step0 raw8593step0Labels = mixedMoment B raw8593step1 raw8593step1Labels := by
      have ha : raw8593step1 = (fun i j => raw8593step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8593step1 raw8593step0; decide +kernel
      have hl : raw8593step1Labels = raw8593step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8593step0 raw8593step0Labels permutation38 permutation7
    mixedMoment B raw8593step1 raw8593step1Labels = mixedMoment B raw8593step2 raw8593step2Labels := by
      have ha : raw8593step2 = raw8593step1 := by apply Matrix.ext; unfold raw8593step2 raw8593step1; decide +kernel
      have hl : raw8593step1Labels = labelEmbedding1 ∘ raw8593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8593step1 raw8593step1Labels raw8593step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw8594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw8594step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw8594step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8594step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw8594step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8594 raw8594Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw8594 raw8594Labels = mixedMoment B raw8594step0 raw8594step0Labels := by
      have hz : ∀ j, raw8594 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8594step0 = (fun i j => raw8594 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8594step0 raw8594; decide +kernel
      have hl : raw8594step0Labels = raw8594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8594 raw8594Labels permutation265 hz
    mixedMoment B raw8594step0 raw8594step0Labels = mixedMoment B raw8594step1 raw8594step1Labels := by
      have ha : raw8594step1 = (fun i j => raw8594step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8594step1 raw8594step0; decide +kernel
      have hl : raw8594step1Labels = raw8594step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8594step0 raw8594step0Labels permutation48 permutation5
    mixedMoment B raw8594step1 raw8594step1Labels = mixedMoment B raw8594step2 raw8594step2Labels := by
      have ha : raw8594step2 = -raw8594step1 := by apply Matrix.ext; change ∀ i j, raw8594step2 i j = -(raw8594step1 i j); unfold raw8594step2 raw8594step1; decide +kernel
      have hl : raw8594step2Labels = raw8594step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8594step2 raw8594step2Labels = mixedMoment B raw8594step3 raw8594step3Labels := by
      have ha : raw8594step3 = raw8594step2 := by apply Matrix.ext; unfold raw8594step3 raw8594step2; decide +kernel
      have hl : raw8594step2Labels = labelEmbedding1 ∘ raw8594step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8594step2 raw8594step2Labels raw8594step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw8595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8595step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8595 raw8595Labels = mixedMoment B node3026 node3026Labels := by
  calc
    mixedMoment B raw8595 raw8595Labels = mixedMoment B raw8595step0 raw8595step0Labels := by
      have hz : ∀ j, raw8595 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8595step0 = (fun i j => raw8595 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8595step0 raw8595; decide +kernel
      have hl : raw8595step0Labels = raw8595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8595 raw8595Labels permutation265 hz
    mixedMoment B raw8595step0 raw8595step0Labels = mixedMoment B raw8595step1 raw8595step1Labels := by
      have ha : raw8595step1 = (fun i j => raw8595step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8595step1 raw8595step0; decide +kernel
      have hl : raw8595step1Labels = raw8595step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8595step0 raw8595step0Labels permutation38 permutation7
    mixedMoment B raw8595step1 raw8595step1Labels = mixedMoment B raw8595step2 raw8595step2Labels := by
      have ha : raw8595step2 = raw8595step1 := by apply Matrix.ext; unfold raw8595step2 raw8595step1; decide +kernel
      have hl : raw8595step1Labels = labelEmbedding1 ∘ raw8595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8595step1 raw8595step1Labels raw8595step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3026 node3026Labels := by rfl

def raw8596 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw8596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw8596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8596 raw8596Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw8596 raw8596Labels = mixedMoment B raw8596step0 raw8596step0Labels := by
      have hz : ∀ j, raw8596 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8596step0 = (fun i j => raw8596 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8596step0 raw8596; decide +kernel
      have hl : raw8596step0Labels = raw8596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8596 raw8596Labels permutation265 hz
    mixedMoment B raw8596step0 raw8596step0Labels = mixedMoment B raw8596step1 raw8596step1Labels := by
      have ha : raw8596step1 = (fun i j => raw8596step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8596step1 raw8596step0; decide +kernel
      have hl : raw8596step1Labels = raw8596step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8596step0 raw8596step0Labels permutation38 permutation7
    mixedMoment B raw8596step1 raw8596step1Labels = mixedMoment B raw8596step2 raw8596step2Labels := by
      have ha : raw8596step2 = raw8596step1 := by apply Matrix.ext; unfold raw8596step2 raw8596step1; decide +kernel
      have hl : raw8596step1Labels = labelEmbedding1 ∘ raw8596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8596step1 raw8596step1Labels raw8596step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw8597 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8597step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8597step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw8597step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw8597step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8597 raw8597Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw8597 raw8597Labels = mixedMoment B raw8597step0 raw8597step0Labels := by
      have hz : ∀ j, raw8597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8597step0 = (fun i j => raw8597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8597step0 raw8597; decide +kernel
      have hl : raw8597step0Labels = raw8597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8597 raw8597Labels permutation346 hz
    mixedMoment B raw8597step0 raw8597step0Labels = mixedMoment B raw8597step1 raw8597step1Labels := by
      have hz : ∀ j, raw8597step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8597step1 = (fun i j => raw8597step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8597step1 raw8597step0; decide +kernel
      have hl : raw8597step1Labels = raw8597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8597step0 raw8597step0Labels permutation56 hz
    mixedMoment B raw8597step1 raw8597step1Labels = mixedMoment B raw8597step2 raw8597step2Labels := by
      have ha : raw8597step2 = (fun i j => raw8597step1 (permutation19 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8597step2 raw8597step1; decide +kernel
      have hl : raw8597step2Labels = raw8597step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8597step1 raw8597step1Labels permutation19 permutation5
    mixedMoment B raw8597step2 raw8597step2Labels = mixedMoment B raw8597step3 raw8597step3Labels := by
      have ha : raw8597step3 = raw8597step2 := by apply Matrix.ext; unfold raw8597step3 raw8597step2; decide +kernel
      have hl : raw8597step2Labels = labelEmbedding1 ∘ raw8597step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8597step2 raw8597step2Labels raw8597step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2113 node2113Labels := by rfl

def raw8598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8598step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8598 raw8598Labels = mixedMoment B node2111 node2111Labels := by
  calc
    mixedMoment B raw8598 raw8598Labels = mixedMoment B raw8598step0 raw8598step0Labels := by
      have hz : ∀ j, raw8598 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8598step0 = (fun i j => raw8598 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8598step0 raw8598; decide +kernel
      have hl : raw8598step0Labels = raw8598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8598 raw8598Labels permutation265 hz
    mixedMoment B raw8598step0 raw8598step0Labels = mixedMoment B raw8598step1 raw8598step1Labels := by
      have ha : raw8598step1 = (fun i j => raw8598step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8598step1 raw8598step0; decide +kernel
      have hl : raw8598step1Labels = raw8598step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8598step0 raw8598step0Labels permutation101 permutation5
    mixedMoment B raw8598step1 raw8598step1Labels = mixedMoment B raw8598step2 raw8598step2Labels := by
      have ha : raw8598step2 = raw8598step1 := by apply Matrix.ext; unfold raw8598step2 raw8598step1; decide +kernel
      have hl : raw8598step1Labels = labelEmbedding1 ∘ raw8598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8598step1 raw8598step1Labels raw8598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2111 node2111Labels := by rfl

def raw8599 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8599step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8599step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8599step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8599step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8599 raw8599Labels = mixedMoment B node2114 node2114Labels := by
  calc
    mixedMoment B raw8599 raw8599Labels = mixedMoment B raw8599step0 raw8599step0Labels := by
      have hz : ∀ j, raw8599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8599step0 = (fun i j => raw8599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8599step0 raw8599; decide +kernel
      have hl : raw8599step0Labels = raw8599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8599 raw8599Labels permutation346 hz
    mixedMoment B raw8599step0 raw8599step0Labels = mixedMoment B raw8599step1 raw8599step1Labels := by
      have hz : ∀ j, raw8599step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8599step1 = (fun i j => raw8599step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8599step1 raw8599step0; decide +kernel
      have hl : raw8599step1Labels = raw8599step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8599step0 raw8599step0Labels permutation56 hz
    mixedMoment B raw8599step1 raw8599step1Labels = mixedMoment B raw8599step2 raw8599step2Labels := by
      have ha : raw8599step2 = (fun i j => raw8599step1 (permutation18 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8599step2 raw8599step1; decide +kernel
      have hl : raw8599step2Labels = raw8599step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8599step1 raw8599step1Labels permutation18 permutation5
    mixedMoment B raw8599step2 raw8599step2Labels = mixedMoment B raw8599step3 raw8599step3Labels := by
      have ha : raw8599step3 = raw8599step2 := by apply Matrix.ext; unfold raw8599step3 raw8599step2; decide +kernel
      have hl : raw8599step2Labels = labelEmbedding1 ∘ raw8599step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8599step2 raw8599step2Labels raw8599step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2114 node2114Labels := by rfl

def raw8600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8600step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8600step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8600step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8600step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8600 raw8600Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw8600 raw8600Labels = mixedMoment B raw8600step0 raw8600step0Labels := by
      have hz : ∀ j, raw8600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8600step0 = (fun i j => raw8600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8600step0 raw8600; decide +kernel
      have hl : raw8600step0Labels = raw8600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8600 raw8600Labels permutation346 hz
    mixedMoment B raw8600step0 raw8600step0Labels = mixedMoment B raw8600step1 raw8600step1Labels := by
      have hz : ∀ j, raw8600step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8600step1 = (fun i j => raw8600step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8600step1 raw8600step0; decide +kernel
      have hl : raw8600step1Labels = raw8600step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8600step0 raw8600step0Labels permutation56 hz
    mixedMoment B raw8600step1 raw8600step1Labels = mixedMoment B raw8600step2 raw8600step2Labels := by
      have ha : raw8600step2 = (fun i j => raw8600step1 (permutation19 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8600step2 raw8600step1; decide +kernel
      have hl : raw8600step2Labels = raw8600step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8600step1 raw8600step1Labels permutation19 permutation5
    mixedMoment B raw8600step2 raw8600step2Labels = mixedMoment B raw8600step3 raw8600step3Labels := by
      have ha : raw8600step3 = raw8600step2 := by apply Matrix.ext; unfold raw8600step3 raw8600step2; decide +kernel
      have hl : raw8600step2Labels = labelEmbedding1 ∘ raw8600step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8600step2 raw8600step2Labels raw8600step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw8601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8601step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw8601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw8601step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8601step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw8601step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8601 raw8601Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw8601 raw8601Labels = mixedMoment B raw8601step0 raw8601step0Labels := by
      have hz : ∀ j, raw8601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8601step0 = (fun i j => raw8601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8601step0 raw8601; decide +kernel
      have hl : raw8601step0Labels = raw8601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8601 raw8601Labels permutation346 hz
    mixedMoment B raw8601step0 raw8601step0Labels = mixedMoment B raw8601step1 raw8601step1Labels := by
      have hz : ∀ j, raw8601step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8601step1 = (fun i j => raw8601step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8601step1 raw8601step0; decide +kernel
      have hl : raw8601step1Labels = raw8601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8601step0 raw8601step0Labels permutation56 hz
    mixedMoment B raw8601step1 raw8601step1Labels = mixedMoment B raw8601step2 raw8601step2Labels := by
      have ha : raw8601step2 = (fun i j => raw8601step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8601step2 raw8601step1; decide +kernel
      have hl : raw8601step2Labels = raw8601step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8601step1 raw8601step1Labels permutation11 permutation5
    mixedMoment B raw8601step2 raw8601step2Labels = mixedMoment B raw8601step3 raw8601step3Labels := by
      have ha : raw8601step3 = -raw8601step2 := by apply Matrix.ext; change ∀ i j, raw8601step3 i j = -(raw8601step2 i j); unfold raw8601step3 raw8601step2; decide +kernel
      have hl : raw8601step3Labels = raw8601step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8601step3 raw8601step3Labels = mixedMoment B raw8601step4 raw8601step4Labels := by
      have ha : raw8601step4 = raw8601step3 := by apply Matrix.ext; unfold raw8601step4 raw8601step3; decide +kernel
      have hl : raw8601step3Labels = labelEmbedding1 ∘ raw8601step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8601step3 raw8601step3Labels raw8601step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3187 node3187Labels := by rfl

def raw8602 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8602step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8602 raw8602Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw8602 raw8602Labels = mixedMoment B raw8602step0 raw8602step0Labels := by
      have hz : ∀ j, raw8602 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8602step0 = (fun i j => raw8602 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8602step0 raw8602; decide +kernel
      have hl : raw8602step0Labels = raw8602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8602 raw8602Labels permutation265 hz
    mixedMoment B raw8602step0 raw8602step0Labels = mixedMoment B raw8602step1 raw8602step1Labels := by
      have ha : raw8602step1 = (fun i j => raw8602step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8602step1 raw8602step0; decide +kernel
      have hl : raw8602step1Labels = raw8602step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8602step0 raw8602step0Labels permutation38 permutation7
    mixedMoment B raw8602step1 raw8602step1Labels = mixedMoment B raw8602step2 raw8602step2Labels := by
      have ha : raw8602step2 = raw8602step1 := by apply Matrix.ext; unfold raw8602step2 raw8602step1; decide +kernel
      have hl : raw8602step1Labels = labelEmbedding1 ∘ raw8602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8602step1 raw8602step1Labels raw8602step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw8603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8603step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8603step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw8603step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8603step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw8603step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8603 raw8603Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw8603 raw8603Labels = mixedMoment B raw8603step0 raw8603step0Labels := by
      have hz : ∀ j, raw8603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8603step0 = (fun i j => raw8603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8603step0 raw8603; decide +kernel
      have hl : raw8603step0Labels = raw8603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8603 raw8603Labels permutation346 hz
    mixedMoment B raw8603step0 raw8603step0Labels = mixedMoment B raw8603step1 raw8603step1Labels := by
      have hz : ∀ j, raw8603step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8603step1 = (fun i j => raw8603step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8603step1 raw8603step0; decide +kernel
      have hl : raw8603step1Labels = raw8603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8603step0 raw8603step0Labels permutation56 hz
    mixedMoment B raw8603step1 raw8603step1Labels = mixedMoment B raw8603step2 raw8603step2Labels := by
      have ha : raw8603step2 = (fun i j => raw8603step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8603step2 raw8603step1; decide +kernel
      have hl : raw8603step2Labels = raw8603step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8603step1 raw8603step1Labels permutation8 permutation7
    mixedMoment B raw8603step2 raw8603step2Labels = mixedMoment B raw8603step3 raw8603step3Labels := by
      have ha : raw8603step3 = raw8603step2 := by apply Matrix.ext; unfold raw8603step3 raw8603step2; decide +kernel
      have hl : raw8603step2Labels = labelEmbedding1 ∘ raw8603step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8603step2 raw8603step2Labels raw8603step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3056 node3056Labels := by rfl

def raw8604 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8604step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8604 raw8604Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw8604 raw8604Labels = mixedMoment B raw8604step0 raw8604step0Labels := by
      have hz : ∀ j, raw8604 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8604step0 = (fun i j => raw8604 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8604step0 raw8604; decide +kernel
      have hl : raw8604step0Labels = raw8604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8604 raw8604Labels permutation265 hz
    mixedMoment B raw8604step0 raw8604step0Labels = mixedMoment B raw8604step1 raw8604step1Labels := by
      have ha : raw8604step1 = (fun i j => raw8604step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8604step1 raw8604step0; decide +kernel
      have hl : raw8604step1Labels = raw8604step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8604step0 raw8604step0Labels permutation39 permutation2
    mixedMoment B raw8604step1 raw8604step1Labels = mixedMoment B raw8604step2 raw8604step2Labels := by
      have ha : raw8604step2 = -raw8604step1 := by apply Matrix.ext; change ∀ i j, raw8604step2 i j = -(raw8604step1 i j); unfold raw8604step2 raw8604step1; decide +kernel
      have hl : raw8604step2Labels = raw8604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3392 node3392Labels := by rfl

def raw8605 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw8605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8605 raw8605Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw8605 raw8605Labels = mixedMoment B raw8605step0 raw8605step0Labels := by
      have hz : ∀ j, raw8605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8605step0 = (fun i j => raw8605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8605step0 raw8605; decide +kernel
      have hl : raw8605step0Labels = raw8605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8605 raw8605Labels permutation346 hz
    mixedMoment B raw8605step0 raw8605step0Labels = mixedMoment B raw8605step1 raw8605step1Labels := by
      have hz : ∀ j, raw8605step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8605step1 = (fun i j => raw8605step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8605step1 raw8605step0; decide +kernel
      have hl : raw8605step1Labels = raw8605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8605step0 raw8605step0Labels permutation56 hz
    mixedMoment B raw8605step1 raw8605step1Labels = mixedMoment B raw8605step2 raw8605step2Labels := by
      have ha : raw8605step2 = (fun i j => raw8605step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8605step2 raw8605step1; decide +kernel
      have hl : raw8605step2Labels = raw8605step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8605step1 raw8605step1Labels permutation25 permutation2
    _ = mixedMoment B node2888 node2888Labels := by rfl

def raw8606 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw8606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8606 raw8606Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw8606 raw8606Labels = mixedMoment B raw8606step0 raw8606step0Labels := by
      have hz : ∀ j, raw8606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8606step0 = (fun i j => raw8606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8606step0 raw8606; decide +kernel
      have hl : raw8606step0Labels = raw8606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8606 raw8606Labels permutation346 hz
    mixedMoment B raw8606step0 raw8606step0Labels = mixedMoment B raw8606step1 raw8606step1Labels := by
      have hz : ∀ j, raw8606step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8606step1 = (fun i j => raw8606step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8606step1 raw8606step0; decide +kernel
      have hl : raw8606step1Labels = raw8606step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8606step0 raw8606step0Labels permutation56 hz
    mixedMoment B raw8606step1 raw8606step1Labels = mixedMoment B raw8606step2 raw8606step2Labels := by
      have ha : raw8606step2 = -raw8606step1 := by apply Matrix.ext; change ∀ i j, raw8606step2 i j = -(raw8606step1 i j); unfold raw8606step2 raw8606step1; decide +kernel
      have hl : raw8606step2Labels = raw8606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw8607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8607 raw8607Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw8607 raw8607Labels = mixedMoment B raw8607step0 raw8607step0Labels := by
      have hz : ∀ j, raw8607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8607step0 = (fun i j => raw8607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8607step0 raw8607; decide +kernel
      have hl : raw8607step0Labels = raw8607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8607 raw8607Labels permutation346 hz
    mixedMoment B raw8607step0 raw8607step0Labels = mixedMoment B raw8607step1 raw8607step1Labels := by
      have ha : raw8607step1 = (fun i j => raw8607step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8607step1 raw8607step0; decide +kernel
      have hl : raw8607step1Labels = raw8607step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8607step0 raw8607step0Labels permutation45 permutation4
    mixedMoment B raw8607step1 raw8607step1Labels = mixedMoment B raw8607step2 raw8607step2Labels := by
      have ha : raw8607step2 = -raw8607step1 := by apply Matrix.ext; change ∀ i j, raw8607step2 i j = -(raw8607step1 i j); unfold raw8607step2 raw8607step1; decide +kernel
      have hl : raw8607step2Labels = raw8607step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2108 node2108Labels := by rfl

def raw8608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8608 raw8608Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw8608 raw8608Labels = mixedMoment B raw8608step0 raw8608step0Labels := by
      have hz : ∀ j, raw8608 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8608step0 = (fun i j => raw8608 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8608step0 raw8608; decide +kernel
      have hl : raw8608step0Labels = raw8608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8608 raw8608Labels permutation265 hz
    mixedMoment B raw8608step0 raw8608step0Labels = mixedMoment B raw8608step1 raw8608step1Labels := by
      have ha : raw8608step1 = (fun i j => raw8608step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8608step1 raw8608step0; decide +kernel
      have hl : raw8608step1Labels = raw8608step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8608step0 raw8608step0Labels permutation45 permutation4
    mixedMoment B raw8608step1 raw8608step1Labels = mixedMoment B raw8608step2 raw8608step2Labels := by
      have ha : raw8608step2 = -raw8608step1 := by apply Matrix.ext; change ∀ i j, raw8608step2 i j = -(raw8608step1 i j); unfold raw8608step2 raw8608step1; decide +kernel
      have hl : raw8608step2Labels = raw8608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2108 node2108Labels := by rfl

def raw8609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw8609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8609step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw8609step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8609 raw8609Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw8609 raw8609Labels = mixedMoment B raw8609step0 raw8609step0Labels := by
      have hz : ∀ j, raw8609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8609step0 = (fun i j => raw8609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8609step0 raw8609; decide +kernel
      have hl : raw8609step0Labels = raw8609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8609 raw8609Labels permutation346 hz
    mixedMoment B raw8609step0 raw8609step0Labels = mixedMoment B raw8609step1 raw8609step1Labels := by
      have hz : ∀ j, raw8609step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8609step1 = (fun i j => raw8609step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8609step1 raw8609step0; decide +kernel
      have hl : raw8609step1Labels = raw8609step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8609step0 raw8609step0Labels permutation56 hz
    mixedMoment B raw8609step1 raw8609step1Labels = mixedMoment B raw8609step2 raw8609step2Labels := by
      have ha : raw8609step2 = (fun i j => raw8609step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8609step2 raw8609step1; decide +kernel
      have hl : raw8609step2Labels = raw8609step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8609step1 raw8609step1Labels permutation11 permutation4
    mixedMoment B raw8609step2 raw8609step2Labels = mixedMoment B raw8609step3 raw8609step3Labels := by
      have ha : raw8609step3 = -raw8609step2 := by apply Matrix.ext; change ∀ i j, raw8609step3 i j = -(raw8609step2 i j); unfold raw8609step3 raw8609step2; decide +kernel
      have hl : raw8609step3Labels = raw8609step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2113 node2113Labels := by rfl

def raw8610 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8610step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw8610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8610step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8610step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8610 raw8610Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw8610 raw8610Labels = mixedMoment B raw8610step0 raw8610step0Labels := by
      have hz : ∀ j, raw8610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8610step0 = (fun i j => raw8610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8610step0 raw8610; decide +kernel
      have hl : raw8610step0Labels = raw8610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8610 raw8610Labels permutation346 hz
    mixedMoment B raw8610step0 raw8610step0Labels = mixedMoment B raw8610step1 raw8610step1Labels := by
      have hz : ∀ j, raw8610step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8610step1 = (fun i j => raw8610step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8610step1 raw8610step0; decide +kernel
      have hl : raw8610step1Labels = raw8610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8610step0 raw8610step0Labels permutation56 hz
    mixedMoment B raw8610step1 raw8610step1Labels = mixedMoment B raw8610step2 raw8610step2Labels := by
      have ha : raw8610step2 = (fun i j => raw8610step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8610step2 raw8610step1; decide +kernel
      have hl : raw8610step2Labels = raw8610step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8610step1 raw8610step1Labels permutation10 permutation4
    mixedMoment B raw8610step2 raw8610step2Labels = mixedMoment B raw8610step3 raw8610step3Labels := by
      have ha : raw8610step3 = -raw8610step2 := by apply Matrix.ext; change ∀ i j, raw8610step3 i j = -(raw8610step2 i j); unfold raw8610step3 raw8610step2; decide +kernel
      have hl : raw8610step3Labels = raw8610step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw8611 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8611step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8611 raw8611Labels = mixedMoment B node3504 node3504Labels := by
  calc
    mixedMoment B raw8611 raw8611Labels = mixedMoment B raw8611step0 raw8611step0Labels := by
      have ha : raw8611step0 = (fun i j => raw8611 (permutation189 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8611step0 raw8611; decide +kernel
      have hl : raw8611step0Labels = raw8611Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8611 raw8611Labels permutation189 permutation4
    mixedMoment B raw8611step0 raw8611step0Labels = mixedMoment B raw8611step1 raw8611step1Labels := by
      have ha : raw8611step1 = -raw8611step0 := by apply Matrix.ext; change ∀ i j, raw8611step1 i j = -(raw8611step0 i j); unfold raw8611step1 raw8611step0; decide +kernel
      have hl : raw8611step1Labels = raw8611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3504 node3504Labels := by rfl

def raw8612 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8612 raw8612Labels = mixedMoment B node2883 node2883Labels := by
  calc
    mixedMoment B raw8612 raw8612Labels = mixedMoment B raw8612step0 raw8612step0Labels := by
      have hz : ∀ j, raw8612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8612step0 = (fun i j => raw8612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8612step0 raw8612; decide +kernel
      have hl : raw8612step0Labels = raw8612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8612 raw8612Labels permutation346 hz
    mixedMoment B raw8612step0 raw8612step0Labels = mixedMoment B raw8612step1 raw8612step1Labels := by
      have ha : raw8612step1 = (fun i j => raw8612step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8612step1 raw8612step0; decide +kernel
      have hl : raw8612step1Labels = raw8612step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8612step0 raw8612step0Labels permutation124 permutation2
    _ = mixedMoment B node2883 node2883Labels := by rfl

def raw8613 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw8613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8613 raw8613Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw8613 raw8613Labels = mixedMoment B raw8613step0 raw8613step0Labels := by
      have hz : ∀ j, raw8613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8613step0 = (fun i j => raw8613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8613step0 raw8613; decide +kernel
      have hl : raw8613step0Labels = raw8613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8613 raw8613Labels permutation346 hz
    mixedMoment B raw8613step0 raw8613step0Labels = mixedMoment B raw8613step1 raw8613step1Labels := by
      have ha : raw8613step1 = (fun i j => raw8613step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8613step1 raw8613step0; decide +kernel
      have hl : raw8613step1Labels = raw8613step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8613step0 raw8613step0Labels permutation48 permutation4
    mixedMoment B raw8613step1 raw8613step1Labels = mixedMoment B raw8613step2 raw8613step2Labels := by
      have ha : raw8613step2 = -raw8613step1 := by apply Matrix.ext; change ∀ i j, raw8613step2 i j = -(raw8613step1 i j); unfold raw8613step2 raw8613step1; decide +kernel
      have hl : raw8613step2Labels = raw8613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3577 node3577Labels := by rfl

def raw8614 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8614 raw8614Labels = mixedMoment B node3157 node3157Labels := by
  calc
    mixedMoment B raw8614 raw8614Labels = mixedMoment B raw8614step0 raw8614step0Labels := by
      have hz : ∀ j, raw8614 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8614step0 = (fun i j => raw8614 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8614step0 raw8614; decide +kernel
      have hl : raw8614step0Labels = raw8614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8614 raw8614Labels permutation265 hz
    mixedMoment B raw8614step0 raw8614step0Labels = mixedMoment B raw8614step1 raw8614step1Labels := by
      have ha : raw8614step1 = (fun i j => raw8614step0 (permutation81 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8614step1 raw8614step0; decide +kernel
      have hl : raw8614step1Labels = raw8614step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8614step0 raw8614step0Labels permutation81 permutation2
    mixedMoment B raw8614step1 raw8614step1Labels = mixedMoment B raw8614step2 raw8614step2Labels := by
      have ha : raw8614step2 = -raw8614step1 := by apply Matrix.ext; change ∀ i j, raw8614step2 i j = -(raw8614step1 i j); unfold raw8614step2 raw8614step1; decide +kernel
      have hl : raw8614step2Labels = raw8614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3157 node3157Labels := by rfl

def raw8615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 2, -3], ![3, -3, 0]]
def raw8615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8615 raw8615Labels = mixedMoment B node2887 node2887Labels := by
  calc
    mixedMoment B raw8615 raw8615Labels = mixedMoment B raw8615step0 raw8615step0Labels := by
      have hz : ∀ j, raw8615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8615step0 = (fun i j => raw8615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8615step0 raw8615; decide +kernel
      have hl : raw8615step0Labels = raw8615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8615 raw8615Labels permutation346 hz
    mixedMoment B raw8615step0 raw8615step0Labels = mixedMoment B raw8615step1 raw8615step1Labels := by
      have hz : ∀ j, raw8615step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8615step1 = (fun i j => raw8615step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8615step1 raw8615step0; decide +kernel
      have hl : raw8615step1Labels = raw8615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8615step0 raw8615step0Labels permutation56 hz
    mixedMoment B raw8615step1 raw8615step1Labels = mixedMoment B raw8615step2 raw8615step2Labels := by
      have ha : raw8615step2 = (fun i j => raw8615step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8615step2 raw8615step1; decide +kernel
      have hl : raw8615step2Labels = raw8615step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8615step1 raw8615step1Labels permutation24 permutation2
    _ = mixedMoment B node2887 node2887Labels := by rfl

def raw8616 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw8616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8616step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw8616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8616 raw8616Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw8616 raw8616Labels = mixedMoment B raw8616step0 raw8616step0Labels := by
      have hz : ∀ j, raw8616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8616step0 = (fun i j => raw8616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8616step0 raw8616; decide +kernel
      have hl : raw8616step0Labels = raw8616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8616 raw8616Labels permutation346 hz
    mixedMoment B raw8616step0 raw8616step0Labels = mixedMoment B raw8616step1 raw8616step1Labels := by
      have hz : ∀ j, raw8616step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8616step1 = (fun i j => raw8616step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8616step1 raw8616step0; decide +kernel
      have hl : raw8616step1Labels = raw8616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8616step0 raw8616step0Labels permutation56 hz
    mixedMoment B raw8616step1 raw8616step1Labels = mixedMoment B raw8616step2 raw8616step2Labels := by
      have ha : raw8616step2 = (fun i j => raw8616step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8616step2 raw8616step1; decide +kernel
      have hl : raw8616step2Labels = raw8616step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8616step1 raw8616step1Labels permutation14 permutation2
    mixedMoment B raw8616step2 raw8616step2Labels = mixedMoment B raw8616step3 raw8616step3Labels := by
      have ha : raw8616step3 = -raw8616step2 := by apply Matrix.ext; change ∀ i j, raw8616step3 i j = -(raw8616step2 i j); unfold raw8616step3 raw8616step2; decide +kernel
      have hl : raw8616step3Labels = raw8616step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3161 node3161Labels := by rfl

def raw8617 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8617 raw8617Labels = mixedMoment B node2883 node2883Labels := by
  calc
    mixedMoment B raw8617 raw8617Labels = mixedMoment B raw8617step0 raw8617step0Labels := by
      have hz : ∀ j, raw8617 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8617step0 = (fun i j => raw8617 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8617step0 raw8617; decide +kernel
      have hl : raw8617step0Labels = raw8617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8617 raw8617Labels permutation265 hz
    mixedMoment B raw8617step0 raw8617step0Labels = mixedMoment B raw8617step1 raw8617step1Labels := by
      have ha : raw8617step1 = (fun i j => raw8617step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8617step1 raw8617step0; decide +kernel
      have hl : raw8617step1Labels = raw8617step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8617step0 raw8617step0Labels permutation124 permutation2
    _ = mixedMoment B node2883 node2883Labels := by rfl

def raw8618 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw8618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8618 raw8618Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw8618 raw8618Labels = mixedMoment B raw8618step0 raw8618step0Labels := by
      have hz : ∀ j, raw8618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8618step0 = (fun i j => raw8618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8618step0 raw8618; decide +kernel
      have hl : raw8618step0Labels = raw8618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8618 raw8618Labels permutation346 hz
    mixedMoment B raw8618step0 raw8618step0Labels = mixedMoment B raw8618step1 raw8618step1Labels := by
      have hz : ∀ j, raw8618step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8618step1 = (fun i j => raw8618step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8618step1 raw8618step0; decide +kernel
      have hl : raw8618step1Labels = raw8618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8618step0 raw8618step0Labels permutation56 hz
    mixedMoment B raw8618step1 raw8618step1Labels = mixedMoment B raw8618step2 raw8618step2Labels := by
      have ha : raw8618step2 = (fun i j => raw8618step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8618step2 raw8618step1; decide +kernel
      have hl : raw8618step2Labels = raw8618step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8618step1 raw8618step1Labels permutation24 permutation2
    _ = mixedMoment B node3056 node3056Labels := by rfl

def raw8619 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8619Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw8619step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8619 raw8619Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw8619 raw8619Labels = mixedMoment B raw8619step0 raw8619step0Labels := by
      have hz : ∀ j, raw8619 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8619step0 = (fun i j => raw8619 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8619step0 raw8619; decide +kernel
      have hl : raw8619step0Labels = raw8619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8619 raw8619Labels permutation265 hz
    mixedMoment B raw8619step0 raw8619step0Labels = mixedMoment B raw8619step1 raw8619step1Labels := by
      have ha : raw8619step1 = (fun i j => raw8619step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8619step1 raw8619step0; decide +kernel
      have hl : raw8619step1Labels = raw8619step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8619step0 raw8619step0Labels permutation34 permutation4
    mixedMoment B raw8619step1 raw8619step1Labels = mixedMoment B raw8619step2 raw8619step2Labels := by
      have ha : raw8619step2 = -raw8619step1 := by apply Matrix.ext; change ∀ i j, raw8619step2 i j = -(raw8619step1 i j); unfold raw8619step2 raw8619step1; decide +kernel
      have hl : raw8619step2Labels = raw8619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3506 node3506Labels := by rfl

def raw8620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8620step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8620step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8620step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8620step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8620 raw8620Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw8620 raw8620Labels = mixedMoment B raw8620step0 raw8620step0Labels := by
      have hz : ∀ j, raw8620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8620step0 = (fun i j => raw8620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8620step0 raw8620; decide +kernel
      have hl : raw8620step0Labels = raw8620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8620 raw8620Labels permutation346 hz
    mixedMoment B raw8620step0 raw8620step0Labels = mixedMoment B raw8620step1 raw8620step1Labels := by
      have ha : raw8620step1 = (fun i j => raw8620step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8620step1 raw8620step0; decide +kernel
      have hl : raw8620step1Labels = raw8620step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8620step0 raw8620step0Labels permutation151 permutation3
    mixedMoment B raw8620step1 raw8620step1Labels = mixedMoment B raw8620step2 raw8620step2Labels := by
      have ha : raw8620step2 = -raw8620step1 := by apply Matrix.ext; change ∀ i j, raw8620step2 i j = -(raw8620step1 i j); unfold raw8620step2 raw8620step1; decide +kernel
      have hl : raw8620step2Labels = raw8620step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8620step2 raw8620step2Labels = mixedMoment B raw8620step3 raw8620step3Labels := by
      have ha : raw8620step3 = raw8620step2 := by apply Matrix.ext; unfold raw8620step3 raw8620step2; decide +kernel
      have hl : raw8620step2Labels = labelEmbedding6 ∘ raw8620step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8620step2 raw8620step2Labels raw8620step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw8621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8621 raw8621Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw8621 raw8621Labels = mixedMoment B raw8621step0 raw8621step0Labels := by
      have hz : ∀ j, raw8621 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8621step0 = (fun i j => raw8621 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8621step0 raw8621; decide +kernel
      have hl : raw8621step0Labels = raw8621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8621 raw8621Labels permutation265 hz
    mixedMoment B raw8621step0 raw8621step0Labels = mixedMoment B raw8621step1 raw8621step1Labels := by
      have ha : raw8621step1 = (fun i j => raw8621step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8621step1 raw8621step0; decide +kernel
      have hl : raw8621step1Labels = raw8621step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8621step0 raw8621step0Labels permutation151 permutation3
    mixedMoment B raw8621step1 raw8621step1Labels = mixedMoment B raw8621step2 raw8621step2Labels := by
      have ha : raw8621step2 = -raw8621step1 := by apply Matrix.ext; change ∀ i j, raw8621step2 i j = -(raw8621step1 i j); unfold raw8621step2 raw8621step1; decide +kernel
      have hl : raw8621step2Labels = raw8621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8621step2 raw8621step2Labels = mixedMoment B raw8621step3 raw8621step3Labels := by
      have ha : raw8621step3 = raw8621step2 := by apply Matrix.ext; unfold raw8621step3 raw8621step2; decide +kernel
      have hl : raw8621step2Labels = labelEmbedding6 ∘ raw8621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8621step2 raw8621step2Labels raw8621step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw8622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw8622step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8622step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8622step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8622step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8622 raw8622Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw8622 raw8622Labels = mixedMoment B raw8622step0 raw8622step0Labels := by
      have hz : ∀ j, raw8622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8622step0 = (fun i j => raw8622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8622step0 raw8622; decide +kernel
      have hl : raw8622step0Labels = raw8622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8622 raw8622Labels permutation346 hz
    mixedMoment B raw8622step0 raw8622step0Labels = mixedMoment B raw8622step1 raw8622step1Labels := by
      have hz : ∀ j, raw8622step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8622step1 = (fun i j => raw8622step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8622step1 raw8622step0; decide +kernel
      have hl : raw8622step1Labels = raw8622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8622step0 raw8622step0Labels permutation56 hz
    mixedMoment B raw8622step1 raw8622step1Labels = mixedMoment B raw8622step2 raw8622step2Labels := by
      have ha : raw8622step2 = (fun i j => raw8622step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8622step2 raw8622step1; decide +kernel
      have hl : raw8622step2Labels = raw8622step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8622step1 raw8622step1Labels permutation14 permutation4
    mixedMoment B raw8622step2 raw8622step2Labels = mixedMoment B raw8622step3 raw8622step3Labels := by
      have ha : raw8622step3 = -raw8622step2 := by apply Matrix.ext; change ∀ i j, raw8622step3 i j = -(raw8622step2 i j); unfold raw8622step3 raw8622step2; decide +kernel
      have hl : raw8622step3Labels = raw8622step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8622step3 raw8622step3Labels = mixedMoment B raw8622step4 raw8622step4Labels := by
      have ha : raw8622step4 = raw8622step3 := by apply Matrix.ext; unfold raw8622step4 raw8622step3; decide +kernel
      have hl : raw8622step3Labels = labelEmbedding7 ∘ raw8622step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8622step3 raw8622step3Labels raw8622step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw8623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw8623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8623step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw8623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8623 raw8623Labels = mixedMoment B node5456 node5456Labels := by
  calc
    mixedMoment B raw8623 raw8623Labels = mixedMoment B raw8623step0 raw8623step0Labels := by
      have hz : ∀ j, raw8623 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8623step0 = (fun i j => raw8623 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8623step0 raw8623; decide +kernel
      have hl : raw8623step0Labels = raw8623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8623 raw8623Labels permutation520 hz
    mixedMoment B raw8623step0 raw8623step0Labels = mixedMoment B raw8623step1 raw8623step1Labels := by
      have hz : ∀ j, raw8623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8623step1 = (fun i j => raw8623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8623step1 raw8623step0; decide +kernel
      have hl : raw8623step1Labels = raw8623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8623step0 raw8623step0Labels permutation80 hz
    mixedMoment B raw8623step1 raw8623step1Labels = mixedMoment B raw8623step2 raw8623step2Labels := by
      have hz : ∀ j, raw8623step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8623step2 = (fun i j => raw8623step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8623step2 raw8623step1; decide +kernel
      have hl : raw8623step2Labels = raw8623step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8623step1 raw8623step1Labels permutation14 hz
    _ = mixedMoment B node5456 node5456Labels := by rfl

def raw8624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw8624step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw8624step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8624 raw8624Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw8624 raw8624Labels = mixedMoment B raw8624step0 raw8624step0Labels := by
      have hz : ∀ j, raw8624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8624step0 = (fun i j => raw8624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8624step0 raw8624; decide +kernel
      have hl : raw8624step0Labels = raw8624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8624 raw8624Labels permutation346 hz
    mixedMoment B raw8624step0 raw8624step0Labels = mixedMoment B raw8624step1 raw8624step1Labels := by
      have hz : ∀ j, raw8624step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8624step1 = (fun i j => raw8624step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8624step1 raw8624step0; decide +kernel
      have hl : raw8624step1Labels = raw8624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8624step0 raw8624step0Labels permutation56 hz
    mixedMoment B raw8624step1 raw8624step1Labels = mixedMoment B raw8624step2 raw8624step2Labels := by
      have ha : raw8624step2 = (fun i j => raw8624step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8624step2 raw8624step1; decide +kernel
      have hl : raw8624step2Labels = raw8624step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8624step1 raw8624step1Labels permutation17 permutation6
    mixedMoment B raw8624step2 raw8624step2Labels = mixedMoment B raw8624step3 raw8624step3Labels := by
      have ha : raw8624step3 = raw8624step2 := by apply Matrix.ext; unfold raw8624step3 raw8624step2; decide +kernel
      have hl : raw8624step2Labels = labelEmbedding9 ∘ raw8624step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8624step2 raw8624step2Labels raw8624step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw8625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8625step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8625 raw8625Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw8625 raw8625Labels = mixedMoment B raw8625step0 raw8625step0Labels := by
      have hz : ∀ j, raw8625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8625step0 = (fun i j => raw8625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8625step0 raw8625; decide +kernel
      have hl : raw8625step0Labels = raw8625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8625 raw8625Labels permutation346 hz
    mixedMoment B raw8625step0 raw8625step0Labels = mixedMoment B raw8625step1 raw8625step1Labels := by
      have ha : raw8625step1 = (fun i j => raw8625step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8625step1 raw8625step0; decide +kernel
      have hl : raw8625step1Labels = raw8625step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8625step0 raw8625step0Labels permutation38 permutation3
    mixedMoment B raw8625step1 raw8625step1Labels = mixedMoment B raw8625step2 raw8625step2Labels := by
      have ha : raw8625step2 = raw8625step1 := by apply Matrix.ext; unfold raw8625step2 raw8625step1; decide +kernel
      have hl : raw8625step1Labels = labelEmbedding6 ∘ raw8625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8625step1 raw8625step1Labels raw8625step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw8626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw8626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8626 raw8626Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw8626 raw8626Labels = mixedMoment B raw8626step0 raw8626step0Labels := by
      have ha : raw8626step0 = (fun i j => raw8626 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8626step0 raw8626; decide +kernel
      have hl : raw8626step0Labels = raw8626Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8626 raw8626Labels permutation182 permutation2
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw8627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw8627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8627 raw8627Labels = mixedMoment B node5213 node5213Labels := by
  calc
    mixedMoment B raw8627 raw8627Labels = mixedMoment B raw8627step0 raw8627step0Labels := by
      have hz : ∀ j, raw8627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8627step0 = (fun i j => raw8627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8627step0 raw8627; decide +kernel
      have hl : raw8627step0Labels = raw8627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8627 raw8627Labels permutation346 hz
    mixedMoment B raw8627step0 raw8627step0Labels = mixedMoment B raw8627step1 raw8627step1Labels := by
      have ha : raw8627step1 = (fun i j => raw8627step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8627step1 raw8627step0; decide +kernel
      have hl : raw8627step1Labels = raw8627step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8627step0 raw8627step0Labels permutation38 permutation2
    _ = mixedMoment B node5213 node5213Labels := by rfl

def raw8628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw8628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8628 raw8628Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw8628 raw8628Labels = mixedMoment B raw8628step0 raw8628step0Labels := by
      have hz : ∀ j, raw8628 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8628step0 = (fun i j => raw8628 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8628step0 raw8628; decide +kernel
      have hl : raw8628step0Labels = raw8628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8628 raw8628Labels permutation520 hz
    mixedMoment B raw8628step0 raw8628step0Labels = mixedMoment B raw8628step1 raw8628step1Labels := by
      have hz : ∀ j, raw8628step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8628step1 = (fun i j => raw8628step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8628step1 raw8628step0; decide +kernel
      have hl : raw8628step1Labels = raw8628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8628step0 raw8628step0Labels permutation80 hz
    mixedMoment B raw8628step1 raw8628step1Labels = mixedMoment B raw8628step2 raw8628step2Labels := by
      have ha : raw8628step2 = (fun i j => raw8628step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8628step2 raw8628step1; decide +kernel
      have hl : raw8628step2Labels = raw8628step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8628step1 raw8628step1Labels permutation10 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw8629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw8629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8629 raw8629Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw8629 raw8629Labels = mixedMoment B raw8629step0 raw8629step0Labels := by
      have hz : ∀ j, raw8629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8629step0 = (fun i j => raw8629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8629step0 raw8629; decide +kernel
      have hl : raw8629step0Labels = raw8629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8629 raw8629Labels permutation346 hz
    mixedMoment B raw8629step0 raw8629step0Labels = mixedMoment B raw8629step1 raw8629step1Labels := by
      have ha : raw8629step1 = (fun i j => raw8629step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8629step1 raw8629step0; decide +kernel
      have hl : raw8629step1Labels = raw8629step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8629step0 raw8629step0Labels permutation38 permutation2
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw8630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8630step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8630step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8630 raw8630Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw8630 raw8630Labels = mixedMoment B raw8630step0 raw8630step0Labels := by
      have hz : ∀ j, raw8630 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8630step0 = (fun i j => raw8630 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8630step0 raw8630; decide +kernel
      have hl : raw8630step0Labels = raw8630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8630 raw8630Labels permutation265 hz
    mixedMoment B raw8630step0 raw8630step0Labels = mixedMoment B raw8630step1 raw8630step1Labels := by
      have ha : raw8630step1 = (fun i j => raw8630step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8630step1 raw8630step0; decide +kernel
      have hl : raw8630step1Labels = raw8630step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8630step0 raw8630step0Labels permutation38 permutation3
    mixedMoment B raw8630step1 raw8630step1Labels = mixedMoment B raw8630step2 raw8630step2Labels := by
      have ha : raw8630step2 = raw8630step1 := by apply Matrix.ext; unfold raw8630step2 raw8630step1; decide +kernel
      have hl : raw8630step1Labels = labelEmbedding6 ∘ raw8630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8630step1 raw8630step1Labels raw8630step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw8631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw8631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8631 raw8631Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw8631 raw8631Labels = mixedMoment B raw8631step0 raw8631step0Labels := by
      have ha : raw8631step0 = (fun i j => raw8631 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8631step0 raw8631; decide +kernel
      have hl : raw8631step0Labels = raw8631Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8631 raw8631Labels permutation158 permutation2
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw8632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw8632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8632 raw8632Labels = mixedMoment B node5213 node5213Labels := by
  calc
    mixedMoment B raw8632 raw8632Labels = mixedMoment B raw8632step0 raw8632step0Labels := by
      have hz : ∀ j, raw8632 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8632step0 = (fun i j => raw8632 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8632step0 raw8632; decide +kernel
      have hl : raw8632step0Labels = raw8632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8632 raw8632Labels permutation265 hz
    mixedMoment B raw8632step0 raw8632step0Labels = mixedMoment B raw8632step1 raw8632step1Labels := by
      have ha : raw8632step1 = (fun i j => raw8632step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8632step1 raw8632step0; decide +kernel
      have hl : raw8632step1Labels = raw8632step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8632step0 raw8632step0Labels permutation38 permutation2
    _ = mixedMoment B node5213 node5213Labels := by rfl

def raw8633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw8633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8633step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8633 raw8633Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw8633 raw8633Labels = mixedMoment B raw8633step0 raw8633step0Labels := by
      have hz : ∀ j, raw8633 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8633step0 = (fun i j => raw8633 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8633step0 raw8633; decide +kernel
      have hl : raw8633step0Labels = raw8633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8633 raw8633Labels permutation520 hz
    mixedMoment B raw8633step0 raw8633step0Labels = mixedMoment B raw8633step1 raw8633step1Labels := by
      have hz : ∀ j, raw8633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8633step1 = (fun i j => raw8633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8633step1 raw8633step0; decide +kernel
      have hl : raw8633step1Labels = raw8633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8633step0 raw8633step0Labels permutation56 hz
    mixedMoment B raw8633step1 raw8633step1Labels = mixedMoment B raw8633step2 raw8633step2Labels := by
      have ha : raw8633step2 = (fun i j => raw8633step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8633step2 raw8633step1; decide +kernel
      have hl : raw8633step2Labels = raw8633step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8633step1 raw8633step1Labels permutation10 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw8634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw8634step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8634 raw8634Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw8634 raw8634Labels = mixedMoment B raw8634step0 raw8634step0Labels := by
      have hz : ∀ j, raw8634 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8634step0 = (fun i j => raw8634 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8634step0 raw8634; decide +kernel
      have hl : raw8634step0Labels = raw8634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8634 raw8634Labels permutation265 hz
    mixedMoment B raw8634step0 raw8634step0Labels = mixedMoment B raw8634step1 raw8634step1Labels := by
      have ha : raw8634step1 = (fun i j => raw8634step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8634step1 raw8634step0; decide +kernel
      have hl : raw8634step1Labels = raw8634step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8634step0 raw8634step0Labels permutation38 permutation2
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw8635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw8635step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw8635step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8635 raw8635Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw8635 raw8635Labels = mixedMoment B raw8635step0 raw8635step0Labels := by
      have hz : ∀ j, raw8635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8635step0 = (fun i j => raw8635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8635step0 raw8635; decide +kernel
      have hl : raw8635step0Labels = raw8635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8635 raw8635Labels permutation346 hz
    mixedMoment B raw8635step0 raw8635step0Labels = mixedMoment B raw8635step1 raw8635step1Labels := by
      have hz : ∀ j, raw8635step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8635step1 = (fun i j => raw8635step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8635step1 raw8635step0; decide +kernel
      have hl : raw8635step1Labels = raw8635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8635step0 raw8635step0Labels permutation56 hz
    mixedMoment B raw8635step1 raw8635step1Labels = mixedMoment B raw8635step2 raw8635step2Labels := by
      have ha : raw8635step2 = (fun i j => raw8635step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8635step2 raw8635step1; decide +kernel
      have hl : raw8635step2Labels = raw8635step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8635step1 raw8635step1Labels permutation8 permutation3
    mixedMoment B raw8635step2 raw8635step2Labels = mixedMoment B raw8635step3 raw8635step3Labels := by
      have ha : raw8635step3 = raw8635step2 := by apply Matrix.ext; unfold raw8635step3 raw8635step2; decide +kernel
      have hl : raw8635step2Labels = labelEmbedding6 ∘ raw8635step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8635step2 raw8635step2Labels raw8635step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw8636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8636 raw8636Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw8636 raw8636Labels = mixedMoment B raw8636step0 raw8636step0Labels := by
      have hz : ∀ j, raw8636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8636step0 = (fun i j => raw8636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8636step0 raw8636; decide +kernel
      have hl : raw8636step0Labels = raw8636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8636 raw8636Labels permutation346 hz
    mixedMoment B raw8636step0 raw8636step0Labels = mixedMoment B raw8636step1 raw8636step1Labels := by
      have ha : raw8636step1 = (fun i j => raw8636step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8636step1 raw8636step0; decide +kernel
      have hl : raw8636step1Labels = raw8636step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8636step0 raw8636step0Labels permutation34 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw8637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8637step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8637 raw8637Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw8637 raw8637Labels = mixedMoment B raw8637step0 raw8637step0Labels := by
      have hz : ∀ j, raw8637 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8637step0 = (fun i j => raw8637 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8637step0 raw8637; decide +kernel
      have hl : raw8637step0Labels = raw8637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8637 raw8637Labels permutation265 hz
    mixedMoment B raw8637step0 raw8637step0Labels = mixedMoment B raw8637step1 raw8637step1Labels := by
      have ha : raw8637step1 = (fun i j => raw8637step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8637step1 raw8637step0; decide +kernel
      have hl : raw8637step1Labels = raw8637step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8637step0 raw8637step0Labels permutation34 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw8638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw8638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8638step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8638 raw8638Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw8638 raw8638Labels = mixedMoment B raw8638step0 raw8638step0Labels := by
      have hz : ∀ j, raw8638 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8638step0 = (fun i j => raw8638 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8638step0 raw8638; decide +kernel
      have hl : raw8638step0Labels = raw8638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8638 raw8638Labels permutation520 hz
    mixedMoment B raw8638step0 raw8638step0Labels = mixedMoment B raw8638step1 raw8638step1Labels := by
      have hz : ∀ j, raw8638step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8638step1 = (fun i j => raw8638step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8638step1 raw8638step0; decide +kernel
      have hl : raw8638step1Labels = raw8638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8638step0 raw8638step0Labels permutation80 hz
    mixedMoment B raw8638step1 raw8638step1Labels = mixedMoment B raw8638step2 raw8638step2Labels := by
      have hz : ∀ j, raw8638step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8638step2 = (fun i j => raw8638step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8638step2 raw8638step1; decide +kernel
      have hl : raw8638step2Labels = raw8638step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8638step1 raw8638step1Labels permutation14 hz
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw8639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8639 raw8639Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw8639 raw8639Labels = mixedMoment B raw8639step0 raw8639step0Labels := by
      have hz : ∀ j, raw8639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8639step0 = (fun i j => raw8639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8639step0 raw8639; decide +kernel
      have hl : raw8639step0Labels = raw8639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8639 raw8639Labels permutation346 hz
    mixedMoment B raw8639step0 raw8639step0Labels = mixedMoment B raw8639step1 raw8639step1Labels := by
      have hz : ∀ j, raw8639step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8639step1 = (fun i j => raw8639step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8639step1 raw8639step0; decide +kernel
      have hl : raw8639step1Labels = raw8639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8639step0 raw8639step0Labels permutation56 hz
    mixedMoment B raw8639step1 raw8639step1Labels = mixedMoment B raw8639step2 raw8639step2Labels := by
      have ha : raw8639step2 = (fun i j => raw8639step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8639step2 raw8639step1; decide +kernel
      have hl : raw8639step2Labels = raw8639step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8639step1 raw8639step1Labels permutation11 permutation2
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw8640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8640step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw8640step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw8640step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8640 raw8640Labels = mixedMoment B node4575 node4575Labels := by
  calc
    mixedMoment B raw8640 raw8640Labels = mixedMoment B raw8640step0 raw8640step0Labels := by
      have hz : ∀ j, raw8640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8640step0 = (fun i j => raw8640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8640step0 raw8640; decide +kernel
      have hl : raw8640step0Labels = raw8640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8640 raw8640Labels permutation346 hz
    mixedMoment B raw8640step0 raw8640step0Labels = mixedMoment B raw8640step1 raw8640step1Labels := by
      have hz : ∀ j, raw8640step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8640step1 = (fun i j => raw8640step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8640step1 raw8640step0; decide +kernel
      have hl : raw8640step1Labels = raw8640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8640step0 raw8640step0Labels permutation56 hz
    mixedMoment B raw8640step1 raw8640step1Labels = mixedMoment B raw8640step2 raw8640step2Labels := by
      have ha : raw8640step2 = (fun i j => raw8640step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8640step2 raw8640step1; decide +kernel
      have hl : raw8640step2Labels = raw8640step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8640step1 raw8640step1Labels permutation8 permutation3
    mixedMoment B raw8640step2 raw8640step2Labels = mixedMoment B raw8640step3 raw8640step3Labels := by
      have ha : raw8640step3 = raw8640step2 := by apply Matrix.ext; unfold raw8640step3 raw8640step2; decide +kernel
      have hl : raw8640step2Labels = labelEmbedding6 ∘ raw8640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8640step2 raw8640step2Labels raw8640step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4575 node4575Labels := by rfl

def raw8641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8641 raw8641Labels = mixedMoment B node5156 node5156Labels := by
  calc
    mixedMoment B raw8641 raw8641Labels = mixedMoment B raw8641step0 raw8641step0Labels := by
      have hz : ∀ j, raw8641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8641step0 = (fun i j => raw8641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8641step0 raw8641; decide +kernel
      have hl : raw8641step0Labels = raw8641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8641 raw8641Labels permutation346 hz
    _ = mixedMoment B node5156 node5156Labels := by rfl

def raw8642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8642 raw8642Labels = mixedMoment B node5156 node5156Labels := by
  calc
    mixedMoment B raw8642 raw8642Labels = mixedMoment B raw8642step0 raw8642step0Labels := by
      have hz : ∀ j, raw8642 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8642step0 = (fun i j => raw8642 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8642step0 raw8642; decide +kernel
      have hl : raw8642step0Labels = raw8642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8642 raw8642Labels permutation265 hz
    _ = mixedMoment B node5156 node5156Labels := by rfl

def raw8643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8643step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8643 raw8643Labels = mixedMoment B node5214 node5214Labels := by
  calc
    mixedMoment B raw8643 raw8643Labels = mixedMoment B raw8643step0 raw8643step0Labels := by
      have hz : ∀ j, raw8643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8643step0 = (fun i j => raw8643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8643step0 raw8643; decide +kernel
      have hl : raw8643step0Labels = raw8643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8643 raw8643Labels permutation346 hz
    mixedMoment B raw8643step0 raw8643step0Labels = mixedMoment B raw8643step1 raw8643step1Labels := by
      have hz : ∀ j, raw8643step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8643step1 = (fun i j => raw8643step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8643step1 raw8643step0; decide +kernel
      have hl : raw8643step1Labels = raw8643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8643step0 raw8643step0Labels permutation56 hz
    _ = mixedMoment B node5214 node5214Labels := by rfl

def raw8644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw8644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw8644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw8644step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8644step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8644 raw8644Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw8644 raw8644Labels = mixedMoment B raw8644step0 raw8644step0Labels := by
      have hz : ∀ j, raw8644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8644step0 = (fun i j => raw8644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8644step0 raw8644; decide +kernel
      have hl : raw8644step0Labels = raw8644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8644 raw8644Labels permutation346 hz
    mixedMoment B raw8644step0 raw8644step0Labels = mixedMoment B raw8644step1 raw8644step1Labels := by
      have hz : ∀ j, raw8644step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8644step1 = (fun i j => raw8644step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8644step1 raw8644step0; decide +kernel
      have hl : raw8644step1Labels = raw8644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8644step0 raw8644step0Labels permutation56 hz
    mixedMoment B raw8644step1 raw8644step1Labels = mixedMoment B raw8644step2 raw8644step2Labels := by
      have ha : raw8644step2 = (fun i j => raw8644step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8644step2 raw8644step1; decide +kernel
      have hl : raw8644step2Labels = raw8644step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8644step1 raw8644step1Labels permutation9 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw8645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw8645step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8645step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw8645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8645 raw8645Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw8645 raw8645Labels = mixedMoment B raw8645step0 raw8645step0Labels := by
      have hz : ∀ j, raw8645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8645step0 = (fun i j => raw8645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8645step0 raw8645; decide +kernel
      have hl : raw8645step0Labels = raw8645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8645 raw8645Labels permutation346 hz
    mixedMoment B raw8645step0 raw8645step0Labels = mixedMoment B raw8645step1 raw8645step1Labels := by
      have hz : ∀ j, raw8645step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8645step1 = (fun i j => raw8645step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8645step1 raw8645step0; decide +kernel
      have hl : raw8645step1Labels = raw8645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8645step0 raw8645step0Labels permutation56 hz
    mixedMoment B raw8645step1 raw8645step1Labels = mixedMoment B raw8645step2 raw8645step2Labels := by
      have ha : raw8645step2 = (fun i j => raw8645step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8645step2 raw8645step1; decide +kernel
      have hl : raw8645step2Labels = raw8645step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8645step1 raw8645step1Labels permutation8 permutation3
    mixedMoment B raw8645step2 raw8645step2Labels = mixedMoment B raw8645step3 raw8645step3Labels := by
      have ha : raw8645step3 = raw8645step2 := by apply Matrix.ext; unfold raw8645step3 raw8645step2; decide +kernel
      have hl : raw8645step2Labels = labelEmbedding6 ∘ raw8645step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8645step2 raw8645step2Labels raw8645step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

def raw8646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8646step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8646step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8646step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8646step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8646 raw8646Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw8646 raw8646Labels = mixedMoment B raw8646step0 raw8646step0Labels := by
      have hz : ∀ j, raw8646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8646step0 = (fun i j => raw8646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8646step0 raw8646; decide +kernel
      have hl : raw8646step0Labels = raw8646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8646 raw8646Labels permutation346 hz
    mixedMoment B raw8646step0 raw8646step0Labels = mixedMoment B raw8646step1 raw8646step1Labels := by
      have ha : raw8646step1 = (fun i j => raw8646step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8646step1 raw8646step0; decide +kernel
      have hl : raw8646step1Labels = raw8646step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8646step0 raw8646step0Labels permutation151 permutation3
    mixedMoment B raw8646step1 raw8646step1Labels = mixedMoment B raw8646step2 raw8646step2Labels := by
      have ha : raw8646step2 = -raw8646step1 := by apply Matrix.ext; change ∀ i j, raw8646step2 i j = -(raw8646step1 i j); unfold raw8646step2 raw8646step1; decide +kernel
      have hl : raw8646step2Labels = raw8646step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8646step2 raw8646step2Labels = mixedMoment B raw8646step3 raw8646step3Labels := by
      have ha : raw8646step3 = raw8646step2 := by apply Matrix.ext; unfold raw8646step3 raw8646step2; decide +kernel
      have hl : raw8646step2Labels = labelEmbedding6 ∘ raw8646step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8646step2 raw8646step2Labels raw8646step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw8647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8647step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8647step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8647step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8647step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8647 raw8647Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw8647 raw8647Labels = mixedMoment B raw8647step0 raw8647step0Labels := by
      have hz : ∀ j, raw8647 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8647step0 = (fun i j => raw8647 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8647step0 raw8647; decide +kernel
      have hl : raw8647step0Labels = raw8647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8647 raw8647Labels permutation265 hz
    mixedMoment B raw8647step0 raw8647step0Labels = mixedMoment B raw8647step1 raw8647step1Labels := by
      have ha : raw8647step1 = (fun i j => raw8647step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8647step1 raw8647step0; decide +kernel
      have hl : raw8647step1Labels = raw8647step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8647step0 raw8647step0Labels permutation151 permutation3
    mixedMoment B raw8647step1 raw8647step1Labels = mixedMoment B raw8647step2 raw8647step2Labels := by
      have ha : raw8647step2 = -raw8647step1 := by apply Matrix.ext; change ∀ i j, raw8647step2 i j = -(raw8647step1 i j); unfold raw8647step2 raw8647step1; decide +kernel
      have hl : raw8647step2Labels = raw8647step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8647step2 raw8647step2Labels = mixedMoment B raw8647step3 raw8647step3Labels := by
      have ha : raw8647step3 = raw8647step2 := by apply Matrix.ext; unfold raw8647step3 raw8647step2; decide +kernel
      have hl : raw8647step2Labels = labelEmbedding6 ∘ raw8647step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8647step2 raw8647step2Labels raw8647step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw8648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw8648step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw8648step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8648step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw8648step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8648 raw8648Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw8648 raw8648Labels = mixedMoment B raw8648step0 raw8648step0Labels := by
      have hz : ∀ j, raw8648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8648step0 = (fun i j => raw8648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8648step0 raw8648; decide +kernel
      have hl : raw8648step0Labels = raw8648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8648 raw8648Labels permutation346 hz
    mixedMoment B raw8648step0 raw8648step0Labels = mixedMoment B raw8648step1 raw8648step1Labels := by
      have hz : ∀ j, raw8648step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8648step1 = (fun i j => raw8648step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8648step1 raw8648step0; decide +kernel
      have hl : raw8648step1Labels = raw8648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8648step0 raw8648step0Labels permutation56 hz
    mixedMoment B raw8648step1 raw8648step1Labels = mixedMoment B raw8648step2 raw8648step2Labels := by
      have ha : raw8648step2 = (fun i j => raw8648step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8648step2 raw8648step1; decide +kernel
      have hl : raw8648step2Labels = raw8648step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8648step1 raw8648step1Labels permutation31 permutation3
    mixedMoment B raw8648step2 raw8648step2Labels = mixedMoment B raw8648step3 raw8648step3Labels := by
      have ha : raw8648step3 = -raw8648step2 := by apply Matrix.ext; change ∀ i j, raw8648step3 i j = -(raw8648step2 i j); unfold raw8648step3 raw8648step2; decide +kernel
      have hl : raw8648step3Labels = raw8648step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8648step3 raw8648step3Labels = mixedMoment B raw8648step4 raw8648step4Labels := by
      have ha : raw8648step4 = raw8648step3 := by apply Matrix.ext; unfold raw8648step4 raw8648step3; decide +kernel
      have hl : raw8648step3Labels = labelEmbedding6 ∘ raw8648step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8648step3 raw8648step3Labels raw8648step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

def raw8649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw8649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw8649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw8649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8649step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw8649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8649step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw8649step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8649step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw8649step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8649step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw8649step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8649 raw8649Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw8649 raw8649Labels = mixedMoment B raw8649step0 raw8649step0Labels := by
      have hz : ∀ j, raw8649 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8649step0 = (fun i j => raw8649 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8649step0 raw8649; decide +kernel
      have hl : raw8649step0Labels = raw8649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8649 raw8649Labels permutation520 hz
    mixedMoment B raw8649step0 raw8649step0Labels = mixedMoment B raw8649step1 raw8649step1Labels := by
      have hz : ∀ j, raw8649step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8649step1 = (fun i j => raw8649step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8649step1 raw8649step0; decide +kernel
      have hl : raw8649step1Labels = raw8649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8649step0 raw8649step0Labels permutation80 hz
    mixedMoment B raw8649step1 raw8649step1Labels = mixedMoment B raw8649step2 raw8649step2Labels := by
      have hz : ∀ j, raw8649step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8649step2 = (fun i j => raw8649step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8649step2 raw8649step1; decide +kernel
      have hl : raw8649step2Labels = raw8649step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8649step1 raw8649step1Labels permutation14 hz
    mixedMoment B raw8649step2 raw8649step2Labels = mixedMoment B raw8649step3 raw8649step3Labels := by
      have ha : raw8649step3 = (fun i j => raw8649step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8649step3 raw8649step2; decide +kernel
      have hl : raw8649step3Labels = raw8649step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8649step2 raw8649step2Labels permutation7 permutation3
    mixedMoment B raw8649step3 raw8649step3Labels = mixedMoment B raw8649step4 raw8649step4Labels := by
      have ha : raw8649step4 = -raw8649step3 := by apply Matrix.ext; change ∀ i j, raw8649step4 i j = -(raw8649step3 i j); unfold raw8649step4 raw8649step3; decide +kernel
      have hl : raw8649step4Labels = raw8649step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8649step4 raw8649step4Labels = mixedMoment B raw8649step5 raw8649step5Labels := by
      have ha : raw8649step5 = raw8649step4 := by apply Matrix.ext; unfold raw8649step5 raw8649step4; decide +kernel
      have hl : raw8649step4Labels = labelEmbedding6 ∘ raw8649step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8649step4 raw8649step4Labels raw8649step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw8650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8650 raw8650Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw8650 raw8650Labels = mixedMoment B raw8650step0 raw8650step0Labels := by
      have hz : ∀ j, raw8650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8650step0 = (fun i j => raw8650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8650step0 raw8650; decide +kernel
      have hl : raw8650step0Labels = raw8650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8650 raw8650Labels permutation346 hz
    mixedMoment B raw8650step0 raw8650step0Labels = mixedMoment B raw8650step1 raw8650step1Labels := by
      have ha : raw8650step1 = (fun i j => raw8650step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8650step1 raw8650step0; decide +kernel
      have hl : raw8650step1Labels = raw8650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8650step0 raw8650step0Labels permutation151 permutation3
    mixedMoment B raw8650step1 raw8650step1Labels = mixedMoment B raw8650step2 raw8650step2Labels := by
      have ha : raw8650step2 = -raw8650step1 := by apply Matrix.ext; change ∀ i j, raw8650step2 i j = -(raw8650step1 i j); unfold raw8650step2 raw8650step1; decide +kernel
      have hl : raw8650step2Labels = raw8650step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw8651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8651 raw8651Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw8651 raw8651Labels = mixedMoment B raw8651step0 raw8651step0Labels := by
      have hz : ∀ j, raw8651 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8651step0 = (fun i j => raw8651 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8651step0 raw8651; decide +kernel
      have hl : raw8651step0Labels = raw8651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8651 raw8651Labels permutation265 hz
    mixedMoment B raw8651step0 raw8651step0Labels = mixedMoment B raw8651step1 raw8651step1Labels := by
      have ha : raw8651step1 = (fun i j => raw8651step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8651step1 raw8651step0; decide +kernel
      have hl : raw8651step1Labels = raw8651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8651step0 raw8651step0Labels permutation151 permutation3
    mixedMoment B raw8651step1 raw8651step1Labels = mixedMoment B raw8651step2 raw8651step2Labels := by
      have ha : raw8651step2 = -raw8651step1 := by apply Matrix.ext; change ∀ i j, raw8651step2 i j = -(raw8651step1 i j); unfold raw8651step2 raw8651step1; decide +kernel
      have hl : raw8651step2Labels = raw8651step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw8652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8652step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw8652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8652 raw8652Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw8652 raw8652Labels = mixedMoment B raw8652step0 raw8652step0Labels := by
      have hz : ∀ j, raw8652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8652step0 = (fun i j => raw8652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8652step0 raw8652; decide +kernel
      have hl : raw8652step0Labels = raw8652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8652 raw8652Labels permutation346 hz
    mixedMoment B raw8652step0 raw8652step0Labels = mixedMoment B raw8652step1 raw8652step1Labels := by
      have hz : ∀ j, raw8652step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8652step1 = (fun i j => raw8652step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8652step1 raw8652step0; decide +kernel
      have hl : raw8652step1Labels = raw8652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8652step0 raw8652step0Labels permutation56 hz
    mixedMoment B raw8652step1 raw8652step1Labels = mixedMoment B raw8652step2 raw8652step2Labels := by
      have ha : raw8652step2 = (fun i j => raw8652step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8652step2 raw8652step1; decide +kernel
      have hl : raw8652step2Labels = raw8652step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8652step1 raw8652step1Labels permutation17 permutation6
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw8653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw8653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8653step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8653step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw8653step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8653step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw8653step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8653step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw8653step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8653 raw8653Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw8653 raw8653Labels = mixedMoment B raw8653step0 raw8653step0Labels := by
      have hz : ∀ j, raw8653 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8653step0 = (fun i j => raw8653 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8653step0 raw8653; decide +kernel
      have hl : raw8653step0Labels = raw8653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8653 raw8653Labels permutation520 hz
    mixedMoment B raw8653step0 raw8653step0Labels = mixedMoment B raw8653step1 raw8653step1Labels := by
      have hz : ∀ j, raw8653step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8653step1 = (fun i j => raw8653step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8653step1 raw8653step0; decide +kernel
      have hl : raw8653step1Labels = raw8653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8653step0 raw8653step0Labels permutation80 hz
    mixedMoment B raw8653step1 raw8653step1Labels = mixedMoment B raw8653step2 raw8653step2Labels := by
      have hz : ∀ j, raw8653step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8653step2 = (fun i j => raw8653step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8653step2 raw8653step1; decide +kernel
      have hl : raw8653step2Labels = raw8653step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8653step1 raw8653step1Labels permutation14 hz
    mixedMoment B raw8653step2 raw8653step2Labels = mixedMoment B raw8653step3 raw8653step3Labels := by
      have ha : raw8653step3 = (fun i j => raw8653step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8653step3 raw8653step2; decide +kernel
      have hl : raw8653step3Labels = raw8653step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8653step2 raw8653step2Labels permutation7 permutation3
    mixedMoment B raw8653step3 raw8653step3Labels = mixedMoment B raw8653step4 raw8653step4Labels := by
      have ha : raw8653step4 = -raw8653step3 := by apply Matrix.ext; change ∀ i j, raw8653step4 i j = -(raw8653step3 i j); unfold raw8653step4 raw8653step3; decide +kernel
      have hl : raw8653step4Labels = raw8653step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3916 node3916Labels := by rfl

def raw8654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8654step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8654step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw8654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8654 raw8654Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw8654 raw8654Labels = mixedMoment B raw8654step0 raw8654step0Labels := by
      have hz : ∀ j, raw8654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8654step0 = (fun i j => raw8654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8654step0 raw8654; decide +kernel
      have hl : raw8654step0Labels = raw8654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8654 raw8654Labels permutation346 hz
    mixedMoment B raw8654step0 raw8654step0Labels = mixedMoment B raw8654step1 raw8654step1Labels := by
      have hz : ∀ j, raw8654step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8654step1 = (fun i j => raw8654step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8654step1 raw8654step0; decide +kernel
      have hl : raw8654step1Labels = raw8654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8654step0 raw8654step0Labels permutation56 hz
    mixedMoment B raw8654step1 raw8654step1Labels = mixedMoment B raw8654step2 raw8654step2Labels := by
      have ha : raw8654step2 = (fun i j => raw8654step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8654step2 raw8654step1; decide +kernel
      have hl : raw8654step2Labels = raw8654step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8654step1 raw8654step1Labels permutation17 permutation6
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw8655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8655 raw8655Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw8655 raw8655Labels = mixedMoment B raw8655step0 raw8655step0Labels := by
      have hz : ∀ j, raw8655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8655step0 = (fun i j => raw8655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8655step0 raw8655; decide +kernel
      have hl : raw8655step0Labels = raw8655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8655 raw8655Labels permutation346 hz
    mixedMoment B raw8655step0 raw8655step0Labels = mixedMoment B raw8655step1 raw8655step1Labels := by
      have ha : raw8655step1 = (fun i j => raw8655step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8655step1 raw8655step0; decide +kernel
      have hl : raw8655step1Labels = raw8655step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8655step0 raw8655step0Labels permutation38 permutation3
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw8656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8656 raw8656Labels = mixedMoment B node2908 node2908Labels := by
  calc
    mixedMoment B raw8656 raw8656Labels = mixedMoment B raw8656step0 raw8656step0Labels := by
      have ha : raw8656step0 = (fun i j => raw8656 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8656step0 raw8656; decide +kernel
      have hl : raw8656step0Labels = raw8656Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8656 raw8656Labels permutation182 permutation3
    _ = mixedMoment B node2908 node2908Labels := by rfl

def raw8657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8657 raw8657Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw8657 raw8657Labels = mixedMoment B raw8657step0 raw8657step0Labels := by
      have hz : ∀ j, raw8657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8657step0 = (fun i j => raw8657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8657step0 raw8657; decide +kernel
      have hl : raw8657step0Labels = raw8657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8657 raw8657Labels permutation346 hz
    mixedMoment B raw8657step0 raw8657step0Labels = mixedMoment B raw8657step1 raw8657step1Labels := by
      have ha : raw8657step1 = (fun i j => raw8657step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8657step1 raw8657step0; decide +kernel
      have hl : raw8657step1Labels = raw8657step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8657step0 raw8657step0Labels permutation38 permutation3
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw8658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw8658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8658step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8658 raw8658Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw8658 raw8658Labels = mixedMoment B raw8658step0 raw8658step0Labels := by
      have hz : ∀ j, raw8658 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8658step0 = (fun i j => raw8658 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8658step0 raw8658; decide +kernel
      have hl : raw8658step0Labels = raw8658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8658 raw8658Labels permutation520 hz
    mixedMoment B raw8658step0 raw8658step0Labels = mixedMoment B raw8658step1 raw8658step1Labels := by
      have hz : ∀ j, raw8658step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8658step1 = (fun i j => raw8658step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8658step1 raw8658step0; decide +kernel
      have hl : raw8658step1Labels = raw8658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8658step0 raw8658step0Labels permutation80 hz
    mixedMoment B raw8658step1 raw8658step1Labels = mixedMoment B raw8658step2 raw8658step2Labels := by
      have ha : raw8658step2 = (fun i j => raw8658step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8658step2 raw8658step1; decide +kernel
      have hl : raw8658step2Labels = raw8658step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8658step1 raw8658step1Labels permutation10 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw8659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw8659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8659 raw8659Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw8659 raw8659Labels = mixedMoment B raw8659step0 raw8659step0Labels := by
      have hz : ∀ j, raw8659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8659step0 = (fun i j => raw8659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8659step0 raw8659; decide +kernel
      have hl : raw8659step0Labels = raw8659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8659 raw8659Labels permutation346 hz
    mixedMoment B raw8659step0 raw8659step0Labels = mixedMoment B raw8659step1 raw8659step1Labels := by
      have ha : raw8659step1 = (fun i j => raw8659step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8659step1 raw8659step0; decide +kernel
      have hl : raw8659step1Labels = raw8659step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8659step0 raw8659step0Labels permutation38 permutation3
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw8660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8660 raw8660Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw8660 raw8660Labels = mixedMoment B raw8660step0 raw8660step0Labels := by
      have hz : ∀ j, raw8660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8660step0 = (fun i j => raw8660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8660step0 raw8660; decide +kernel
      have hl : raw8660step0Labels = raw8660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8660 raw8660Labels permutation265 hz
    mixedMoment B raw8660step0 raw8660step0Labels = mixedMoment B raw8660step1 raw8660step1Labels := by
      have ha : raw8660step1 = (fun i j => raw8660step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8660step1 raw8660step0; decide +kernel
      have hl : raw8660step1Labels = raw8660step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8660step0 raw8660step0Labels permutation38 permutation3
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw8661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8661step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8661 raw8661Labels = mixedMoment B node2908 node2908Labels := by
  calc
    mixedMoment B raw8661 raw8661Labels = mixedMoment B raw8661step0 raw8661step0Labels := by
      have ha : raw8661step0 = (fun i j => raw8661 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8661step0 raw8661; decide +kernel
      have hl : raw8661step0Labels = raw8661Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8661 raw8661Labels permutation158 permutation3
    _ = mixedMoment B node2908 node2908Labels := by rfl

def raw8662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8662 raw8662Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw8662 raw8662Labels = mixedMoment B raw8662step0 raw8662step0Labels := by
      have hz : ∀ j, raw8662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8662step0 = (fun i j => raw8662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8662step0 raw8662; decide +kernel
      have hl : raw8662step0Labels = raw8662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8662 raw8662Labels permutation265 hz
    mixedMoment B raw8662step0 raw8662step0Labels = mixedMoment B raw8662step1 raw8662step1Labels := by
      have ha : raw8662step1 = (fun i j => raw8662step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8662step1 raw8662step0; decide +kernel
      have hl : raw8662step1Labels = raw8662step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8662step0 raw8662step0Labels permutation38 permutation3
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw8663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw8663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8663step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8663 raw8663Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw8663 raw8663Labels = mixedMoment B raw8663step0 raw8663step0Labels := by
      have hz : ∀ j, raw8663 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8663step0 = (fun i j => raw8663 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8663step0 raw8663; decide +kernel
      have hl : raw8663step0Labels = raw8663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8663 raw8663Labels permutation520 hz
    mixedMoment B raw8663step0 raw8663step0Labels = mixedMoment B raw8663step1 raw8663step1Labels := by
      have hz : ∀ j, raw8663step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8663step1 = (fun i j => raw8663step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8663step1 raw8663step0; decide +kernel
      have hl : raw8663step1Labels = raw8663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8663step0 raw8663step0Labels permutation56 hz
    mixedMoment B raw8663step1 raw8663step1Labels = mixedMoment B raw8663step2 raw8663step2Labels := by
      have ha : raw8663step2 = (fun i j => raw8663step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8663step2 raw8663step1; decide +kernel
      have hl : raw8663step2Labels = raw8663step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8663step1 raw8663step1Labels permutation10 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw8664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw8664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8664 raw8664Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw8664 raw8664Labels = mixedMoment B raw8664step0 raw8664step0Labels := by
      have hz : ∀ j, raw8664 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8664step0 = (fun i j => raw8664 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8664step0 raw8664; decide +kernel
      have hl : raw8664step0Labels = raw8664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8664 raw8664Labels permutation265 hz
    mixedMoment B raw8664step0 raw8664step0Labels = mixedMoment B raw8664step1 raw8664step1Labels := by
      have ha : raw8664step1 = (fun i j => raw8664step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8664step1 raw8664step0; decide +kernel
      have hl : raw8664step1Labels = raw8664step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8664step0 raw8664step0Labels permutation38 permutation3
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw8665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8665step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw8665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8665 raw8665Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw8665 raw8665Labels = mixedMoment B raw8665step0 raw8665step0Labels := by
      have hz : ∀ j, raw8665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8665step0 = (fun i j => raw8665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8665step0 raw8665; decide +kernel
      have hl : raw8665step0Labels = raw8665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8665 raw8665Labels permutation346 hz
    mixedMoment B raw8665step0 raw8665step0Labels = mixedMoment B raw8665step1 raw8665step1Labels := by
      have hz : ∀ j, raw8665step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8665step1 = (fun i j => raw8665step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8665step1 raw8665step0; decide +kernel
      have hl : raw8665step1Labels = raw8665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8665step0 raw8665step0Labels permutation56 hz
    mixedMoment B raw8665step1 raw8665step1Labels = mixedMoment B raw8665step2 raw8665step2Labels := by
      have ha : raw8665step2 = (fun i j => raw8665step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8665step2 raw8665step1; decide +kernel
      have hl : raw8665step2Labels = raw8665step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8665step1 raw8665step1Labels permutation8 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw8666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw8666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8666 raw8666Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw8666 raw8666Labels = mixedMoment B raw8666step0 raw8666step0Labels := by
      have hz : ∀ j, raw8666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8666step0 = (fun i j => raw8666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8666step0 raw8666; decide +kernel
      have hl : raw8666step0Labels = raw8666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8666 raw8666Labels permutation346 hz
    mixedMoment B raw8666step0 raw8666step0Labels = mixedMoment B raw8666step1 raw8666step1Labels := by
      have ha : raw8666step1 = (fun i j => raw8666step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8666step1 raw8666step0; decide +kernel
      have hl : raw8666step1Labels = raw8666step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8666step0 raw8666step0Labels permutation32 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw8667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw8667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8667 raw8667Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw8667 raw8667Labels = mixedMoment B raw8667step0 raw8667step0Labels := by
      have hz : ∀ j, raw8667 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8667step0 = (fun i j => raw8667 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8667step0 raw8667; decide +kernel
      have hl : raw8667step0Labels = raw8667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8667 raw8667Labels permutation265 hz
    mixedMoment B raw8667step0 raw8667step0Labels = mixedMoment B raw8667step1 raw8667step1Labels := by
      have ha : raw8667step1 = (fun i j => raw8667step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8667step1 raw8667step0; decide +kernel
      have hl : raw8667step1Labels = raw8667step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8667step0 raw8667step0Labels permutation32 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw8668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw8668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8668step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8668step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8668step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8668step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw8668step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8668 raw8668Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw8668 raw8668Labels = mixedMoment B raw8668step0 raw8668step0Labels := by
      have hz : ∀ j, raw8668 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8668step0 = (fun i j => raw8668 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8668step0 raw8668; decide +kernel
      have hl : raw8668step0Labels = raw8668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8668 raw8668Labels permutation520 hz
    mixedMoment B raw8668step0 raw8668step0Labels = mixedMoment B raw8668step1 raw8668step1Labels := by
      have hz : ∀ j, raw8668step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8668step1 = (fun i j => raw8668step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8668step1 raw8668step0; decide +kernel
      have hl : raw8668step1Labels = raw8668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8668step0 raw8668step0Labels permutation80 hz
    mixedMoment B raw8668step1 raw8668step1Labels = mixedMoment B raw8668step2 raw8668step2Labels := by
      have hz : ∀ j, raw8668step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8668step2 = (fun i j => raw8668step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8668step2 raw8668step1; decide +kernel
      have hl : raw8668step2Labels = raw8668step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8668step1 raw8668step1Labels permutation14 hz
    mixedMoment B raw8668step2 raw8668step2Labels = mixedMoment B raw8668step3 raw8668step3Labels := by
      have ha : raw8668step3 = (fun i j => raw8668step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8668step3 raw8668step2; decide +kernel
      have hl : raw8668step3Labels = raw8668step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8668step2 raw8668step2Labels permutation2 permutation3
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw8669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8669step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8669 raw8669Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw8669 raw8669Labels = mixedMoment B raw8669step0 raw8669step0Labels := by
      have hz : ∀ j, raw8669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8669step0 = (fun i j => raw8669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8669step0 raw8669; decide +kernel
      have hl : raw8669step0Labels = raw8669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8669 raw8669Labels permutation346 hz
    mixedMoment B raw8669step0 raw8669step0Labels = mixedMoment B raw8669step1 raw8669step1Labels := by
      have hz : ∀ j, raw8669step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8669step1 = (fun i j => raw8669step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8669step1 raw8669step0; decide +kernel
      have hl : raw8669step1Labels = raw8669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8669step0 raw8669step0Labels permutation56 hz
    mixedMoment B raw8669step1 raw8669step1Labels = mixedMoment B raw8669step2 raw8669step2Labels := by
      have ha : raw8669step2 = (fun i j => raw8669step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8669step2 raw8669step1; decide +kernel
      have hl : raw8669step2Labels = raw8669step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8669step1 raw8669step1Labels permutation8 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw8670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8670step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw8670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8670 raw8670Labels = mixedMoment B node1193 node1193Labels := by
  calc
    mixedMoment B raw8670 raw8670Labels = mixedMoment B raw8670step0 raw8670step0Labels := by
      have hz : ∀ j, raw8670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8670step0 = (fun i j => raw8670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8670step0 raw8670; decide +kernel
      have hl : raw8670step0Labels = raw8670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8670 raw8670Labels permutation346 hz
    mixedMoment B raw8670step0 raw8670step0Labels = mixedMoment B raw8670step1 raw8670step1Labels := by
      have hz : ∀ j, raw8670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8670step1 = (fun i j => raw8670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8670step1 raw8670step0; decide +kernel
      have hl : raw8670step1Labels = raw8670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8670step0 raw8670step0Labels permutation56 hz
    mixedMoment B raw8670step1 raw8670step1Labels = mixedMoment B raw8670step2 raw8670step2Labels := by
      have ha : raw8670step2 = (fun i j => raw8670step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8670step2 raw8670step1; decide +kernel
      have hl : raw8670step2Labels = raw8670step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8670step1 raw8670step1Labels permutation8 permutation3
    _ = mixedMoment B node1193 node1193Labels := by rfl

def raw8671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw8671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8671 raw8671Labels = mixedMoment B node2911 node2911Labels := by
  calc
    mixedMoment B raw8671 raw8671Labels = mixedMoment B raw8671step0 raw8671step0Labels := by
      have hz : ∀ j, raw8671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8671step0 = (fun i j => raw8671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8671step0 raw8671; decide +kernel
      have hl : raw8671step0Labels = raw8671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8671 raw8671Labels permutation346 hz
    mixedMoment B raw8671step0 raw8671step0Labels = mixedMoment B raw8671step1 raw8671step1Labels := by
      have ha : raw8671step1 = (fun i j => raw8671step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8671step1 raw8671step0; decide +kernel
      have hl : raw8671step1Labels = raw8671step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8671step0 raw8671step0Labels permutation32 permutation3
    _ = mixedMoment B node2911 node2911Labels := by rfl

def raw8672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw8672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8672 raw8672Labels = mixedMoment B node2911 node2911Labels := by
  calc
    mixedMoment B raw8672 raw8672Labels = mixedMoment B raw8672step0 raw8672step0Labels := by
      have hz : ∀ j, raw8672 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8672step0 = (fun i j => raw8672 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8672step0 raw8672; decide +kernel
      have hl : raw8672step0Labels = raw8672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8672 raw8672Labels permutation265 hz
    mixedMoment B raw8672step0 raw8672step0Labels = mixedMoment B raw8672step1 raw8672step1Labels := by
      have ha : raw8672step1 = (fun i j => raw8672step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8672step1 raw8672step0; decide +kernel
      have hl : raw8672step1Labels = raw8672step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8672step0 raw8672step0Labels permutation32 permutation3
    _ = mixedMoment B node2911 node2911Labels := by rfl

def raw8673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8673step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw8673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8673 raw8673Labels = mixedMoment B node2843 node2843Labels := by
  calc
    mixedMoment B raw8673 raw8673Labels = mixedMoment B raw8673step0 raw8673step0Labels := by
      have hz : ∀ j, raw8673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8673step0 = (fun i j => raw8673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8673step0 raw8673; decide +kernel
      have hl : raw8673step0Labels = raw8673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8673 raw8673Labels permutation346 hz
    mixedMoment B raw8673step0 raw8673step0Labels = mixedMoment B raw8673step1 raw8673step1Labels := by
      have hz : ∀ j, raw8673step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8673step1 = (fun i j => raw8673step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8673step1 raw8673step0; decide +kernel
      have hl : raw8673step1Labels = raw8673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8673step0 raw8673step0Labels permutation56 hz
    mixedMoment B raw8673step1 raw8673step1Labels = mixedMoment B raw8673step2 raw8673step2Labels := by
      have ha : raw8673step2 = (fun i j => raw8673step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8673step2 raw8673step1; decide +kernel
      have hl : raw8673step2Labels = raw8673step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8673step1 raw8673step1Labels permutation8 permutation3
    _ = mixedMoment B node2843 node2843Labels := by rfl

def raw8674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw8674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw8674step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw8674step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8674 raw8674Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw8674 raw8674Labels = mixedMoment B raw8674step0 raw8674step0Labels := by
      have hz : ∀ j, raw8674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8674step0 = (fun i j => raw8674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8674step0 raw8674; decide +kernel
      have hl : raw8674step0Labels = raw8674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8674 raw8674Labels permutation346 hz
    mixedMoment B raw8674step0 raw8674step0Labels = mixedMoment B raw8674step1 raw8674step1Labels := by
      have hz : ∀ j, raw8674step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8674step1 = (fun i j => raw8674step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8674step1 raw8674step0; decide +kernel
      have hl : raw8674step1Labels = raw8674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8674step0 raw8674step0Labels permutation56 hz
    mixedMoment B raw8674step1 raw8674step1Labels = mixedMoment B raw8674step2 raw8674step2Labels := by
      have ha : raw8674step2 = (fun i j => raw8674step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8674step2 raw8674step1; decide +kernel
      have hl : raw8674step2Labels = raw8674step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8674step1 raw8674step1Labels permutation9 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw8675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8675step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw8675step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8675 raw8675Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw8675 raw8675Labels = mixedMoment B raw8675step0 raw8675step0Labels := by
      have hz : ∀ j, raw8675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8675step0 = (fun i j => raw8675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8675step0 raw8675; decide +kernel
      have hl : raw8675step0Labels = raw8675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8675 raw8675Labels permutation346 hz
    mixedMoment B raw8675step0 raw8675step0Labels = mixedMoment B raw8675step1 raw8675step1Labels := by
      have hz : ∀ j, raw8675step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8675step1 = (fun i j => raw8675step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8675step1 raw8675step0; decide +kernel
      have hl : raw8675step1Labels = raw8675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8675step0 raw8675step0Labels permutation56 hz
    mixedMoment B raw8675step1 raw8675step1Labels = mixedMoment B raw8675step2 raw8675step2Labels := by
      have ha : raw8675step2 = (fun i j => raw8675step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8675step2 raw8675step1; decide +kernel
      have hl : raw8675step2Labels = raw8675step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8675step1 raw8675step1Labels permutation8 permutation3
    _ = mixedMoment B node1190 node1190Labels := by rfl

def raw8676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8676step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8676step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8676 raw8676Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw8676 raw8676Labels = mixedMoment B raw8676step0 raw8676step0Labels := by
      have hz : ∀ j, raw8676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8676step0 = (fun i j => raw8676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8676step0 raw8676; decide +kernel
      have hl : raw8676step0Labels = raw8676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8676 raw8676Labels permutation346 hz
    mixedMoment B raw8676step0 raw8676step0Labels = mixedMoment B raw8676step1 raw8676step1Labels := by
      have ha : raw8676step1 = (fun i j => raw8676step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8676step1 raw8676step0; decide +kernel
      have hl : raw8676step1Labels = raw8676step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8676step0 raw8676step0Labels permutation151 permutation3
    mixedMoment B raw8676step1 raw8676step1Labels = mixedMoment B raw8676step2 raw8676step2Labels := by
      have ha : raw8676step2 = -raw8676step1 := by apply Matrix.ext; change ∀ i j, raw8676step2 i j = -(raw8676step1 i j); unfold raw8676step2 raw8676step1; decide +kernel
      have hl : raw8676step2Labels = raw8676step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw8677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8677 raw8677Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw8677 raw8677Labels = mixedMoment B raw8677step0 raw8677step0Labels := by
      have hz : ∀ j, raw8677 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8677step0 = (fun i j => raw8677 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8677step0 raw8677; decide +kernel
      have hl : raw8677step0Labels = raw8677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8677 raw8677Labels permutation265 hz
    mixedMoment B raw8677step0 raw8677step0Labels = mixedMoment B raw8677step1 raw8677step1Labels := by
      have ha : raw8677step1 = (fun i j => raw8677step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8677step1 raw8677step0; decide +kernel
      have hl : raw8677step1Labels = raw8677step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8677step0 raw8677step0Labels permutation151 permutation3
    mixedMoment B raw8677step1 raw8677step1Labels = mixedMoment B raw8677step2 raw8677step2Labels := by
      have ha : raw8677step2 = -raw8677step1 := by apply Matrix.ext; change ∀ i j, raw8677step2 i j = -(raw8677step1 i j); unfold raw8677step2 raw8677step1; decide +kernel
      have hl : raw8677step2Labels = raw8677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw8678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8678step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw8678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8678step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw8678step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8678 raw8678Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw8678 raw8678Labels = mixedMoment B raw8678step0 raw8678step0Labels := by
      have hz : ∀ j, raw8678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8678step0 = (fun i j => raw8678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8678step0 raw8678; decide +kernel
      have hl : raw8678step0Labels = raw8678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8678 raw8678Labels permutation346 hz
    mixedMoment B raw8678step0 raw8678step0Labels = mixedMoment B raw8678step1 raw8678step1Labels := by
      have hz : ∀ j, raw8678step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8678step1 = (fun i j => raw8678step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8678step1 raw8678step0; decide +kernel
      have hl : raw8678step1Labels = raw8678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8678step0 raw8678step0Labels permutation56 hz
    mixedMoment B raw8678step1 raw8678step1Labels = mixedMoment B raw8678step2 raw8678step2Labels := by
      have ha : raw8678step2 = (fun i j => raw8678step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8678step2 raw8678step1; decide +kernel
      have hl : raw8678step2Labels = raw8678step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8678step1 raw8678step1Labels permutation31 permutation3
    mixedMoment B raw8678step2 raw8678step2Labels = mixedMoment B raw8678step3 raw8678step3Labels := by
      have ha : raw8678step3 = -raw8678step2 := by apply Matrix.ext; change ∀ i j, raw8678step3 i j = -(raw8678step2 i j); unfold raw8678step3 raw8678step2; decide +kernel
      have hl : raw8678step3Labels = raw8678step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1951 node1951Labels := by rfl

def raw8679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw8679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw8679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw8679step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8679step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw8679step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8679step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw8679step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8679step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw8679step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8679 raw8679Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw8679 raw8679Labels = mixedMoment B raw8679step0 raw8679step0Labels := by
      have hz : ∀ j, raw8679 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw8679step0 = (fun i j => raw8679 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw8679step0 raw8679; decide +kernel
      have hl : raw8679step0Labels = raw8679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8679 raw8679Labels permutation520 hz
    mixedMoment B raw8679step0 raw8679step0Labels = mixedMoment B raw8679step1 raw8679step1Labels := by
      have hz : ∀ j, raw8679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8679step1 = (fun i j => raw8679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8679step1 raw8679step0; decide +kernel
      have hl : raw8679step1Labels = raw8679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8679step0 raw8679step0Labels permutation80 hz
    mixedMoment B raw8679step1 raw8679step1Labels = mixedMoment B raw8679step2 raw8679step2Labels := by
      have hz : ∀ j, raw8679step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw8679step2 = (fun i j => raw8679step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw8679step2 raw8679step1; decide +kernel
      have hl : raw8679step2Labels = raw8679step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8679step1 raw8679step1Labels permutation14 hz
    mixedMoment B raw8679step2 raw8679step2Labels = mixedMoment B raw8679step3 raw8679step3Labels := by
      have ha : raw8679step3 = (fun i j => raw8679step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8679step3 raw8679step2; decide +kernel
      have hl : raw8679step3Labels = raw8679step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8679step2 raw8679step2Labels permutation7 permutation3
    mixedMoment B raw8679step3 raw8679step3Labels = mixedMoment B raw8679step4 raw8679step4Labels := by
      have ha : raw8679step4 = -raw8679step3 := by apply Matrix.ext; change ∀ i j, raw8679step4 i j = -(raw8679step3 i j); unfold raw8679step4 raw8679step3; decide +kernel
      have hl : raw8679step4Labels = raw8679step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw8680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8680step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8680 raw8680Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw8680 raw8680Labels = mixedMoment B raw8680step0 raw8680step0Labels := by
      have hz : ∀ j, raw8680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8680step0 = (fun i j => raw8680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8680step0 raw8680; decide +kernel
      have hl : raw8680step0Labels = raw8680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8680 raw8680Labels permutation346 hz
    mixedMoment B raw8680step0 raw8680step0Labels = mixedMoment B raw8680step1 raw8680step1Labels := by
      have ha : raw8680step1 = (fun i j => raw8680step0 (permutation148 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8680step1 raw8680step0; decide +kernel
      have hl : raw8680step1Labels = raw8680step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8680step0 raw8680step0Labels permutation148 permutation7
    mixedMoment B raw8680step1 raw8680step1Labels = mixedMoment B raw8680step2 raw8680step2Labels := by
      have ha : raw8680step2 = raw8680step1 := by apply Matrix.ext; unfold raw8680step2 raw8680step1; decide +kernel
      have hl : raw8680step1Labels = labelEmbedding10 ∘ raw8680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8680step1 raw8680step1Labels raw8680step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw8681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8681step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8681 raw8681Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw8681 raw8681Labels = mixedMoment B raw8681step0 raw8681step0Labels := by
      have hz : ∀ j, raw8681 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8681step0 = (fun i j => raw8681 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8681step0 raw8681; decide +kernel
      have hl : raw8681step0Labels = raw8681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8681 raw8681Labels permutation265 hz
    mixedMoment B raw8681step0 raw8681step0Labels = mixedMoment B raw8681step1 raw8681step1Labels := by
      have ha : raw8681step1 = (fun i j => raw8681step0 (permutation148 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8681step1 raw8681step0; decide +kernel
      have hl : raw8681step1Labels = raw8681step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8681step0 raw8681step0Labels permutation148 permutation7
    mixedMoment B raw8681step1 raw8681step1Labels = mixedMoment B raw8681step2 raw8681step2Labels := by
      have ha : raw8681step2 = raw8681step1 := by apply Matrix.ext; unfold raw8681step2 raw8681step1; decide +kernel
      have hl : raw8681step1Labels = labelEmbedding10 ∘ raw8681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8681step1 raw8681step1Labels raw8681step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw8682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8682step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8682step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8682 raw8682Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw8682 raw8682Labels = mixedMoment B raw8682step0 raw8682step0Labels := by
      have hz : ∀ j, raw8682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8682step0 = (fun i j => raw8682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8682step0 raw8682; decide +kernel
      have hl : raw8682step0Labels = raw8682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8682 raw8682Labels permutation346 hz
    mixedMoment B raw8682step0 raw8682step0Labels = mixedMoment B raw8682step1 raw8682step1Labels := by
      have hz : ∀ j, raw8682step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8682step1 = (fun i j => raw8682step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8682step1 raw8682step0; decide +kernel
      have hl : raw8682step1Labels = raw8682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8682step0 raw8682step0Labels permutation56 hz
    mixedMoment B raw8682step1 raw8682step1Labels = mixedMoment B raw8682step2 raw8682step2Labels := by
      have ha : raw8682step2 = (fun i j => raw8682step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8682step2 raw8682step1; decide +kernel
      have hl : raw8682step2Labels = raw8682step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8682step1 raw8682step1Labels permutation31 permutation2
    mixedMoment B raw8682step2 raw8682step2Labels = mixedMoment B raw8682step3 raw8682step3Labels := by
      have ha : raw8682step3 = -raw8682step2 := by apply Matrix.ext; change ∀ i j, raw8682step3 i j = -(raw8682step2 i j); unfold raw8682step3 raw8682step2; decide +kernel
      have hl : raw8682step3Labels = raw8682step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw8683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8683step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8683 raw8683Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw8683 raw8683Labels = mixedMoment B raw8683step0 raw8683step0Labels := by
      have hz : ∀ j, raw8683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8683step0 = (fun i j => raw8683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8683step0 raw8683; decide +kernel
      have hl : raw8683step0Labels = raw8683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8683 raw8683Labels permutation346 hz
    mixedMoment B raw8683step0 raw8683step0Labels = mixedMoment B raw8683step1 raw8683step1Labels := by
      have hz : ∀ j, raw8683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8683step1 = (fun i j => raw8683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8683step1 raw8683step0; decide +kernel
      have hl : raw8683step1Labels = raw8683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8683step0 raw8683step0Labels permutation56 hz
    mixedMoment B raw8683step1 raw8683step1Labels = mixedMoment B raw8683step2 raw8683step2Labels := by
      have ha : raw8683step2 = (fun i j => raw8683step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8683step2 raw8683step1; decide +kernel
      have hl : raw8683step2Labels = raw8683step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8683step1 raw8683step1Labels permutation30 permutation7
    mixedMoment B raw8683step2 raw8683step2Labels = mixedMoment B raw8683step3 raw8683step3Labels := by
      have ha : raw8683step3 = raw8683step2 := by apply Matrix.ext; unfold raw8683step3 raw8683step2; decide +kernel
      have hl : raw8683step2Labels = labelEmbedding10 ∘ raw8683step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8683step2 raw8683step2Labels raw8683step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw8684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8684step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8684step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8684step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8684step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8684 raw8684Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw8684 raw8684Labels = mixedMoment B raw8684step0 raw8684step0Labels := by
      have hz : ∀ j, raw8684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8684step0 = (fun i j => raw8684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8684step0 raw8684; decide +kernel
      have hl : raw8684step0Labels = raw8684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8684 raw8684Labels permutation346 hz
    mixedMoment B raw8684step0 raw8684step0Labels = mixedMoment B raw8684step1 raw8684step1Labels := by
      have hz : ∀ j, raw8684step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8684step1 = (fun i j => raw8684step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8684step1 raw8684step0; decide +kernel
      have hl : raw8684step1Labels = raw8684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8684step0 raw8684step0Labels permutation56 hz
    mixedMoment B raw8684step1 raw8684step1Labels = mixedMoment B raw8684step2 raw8684step2Labels := by
      have ha : raw8684step2 = (fun i j => raw8684step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8684step2 raw8684step1; decide +kernel
      have hl : raw8684step2Labels = raw8684step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8684step1 raw8684step1Labels permutation14 permutation6
    mixedMoment B raw8684step2 raw8684step2Labels = mixedMoment B raw8684step3 raw8684step3Labels := by
      have ha : raw8684step3 = -raw8684step2 := by apply Matrix.ext; change ∀ i j, raw8684step3 i j = -(raw8684step2 i j); unfold raw8684step3 raw8684step2; decide +kernel
      have hl : raw8684step3Labels = raw8684step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8684step3 raw8684step3Labels = mixedMoment B raw8684step4 raw8684step4Labels := by
      have ha : raw8684step4 = raw8684step3 := by apply Matrix.ext; unfold raw8684step4 raw8684step3; decide +kernel
      have hl : raw8684step3Labels = labelEmbedding9 ∘ raw8684step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8684step3 raw8684step3Labels raw8684step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw8685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8685step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8685 raw8685Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw8685 raw8685Labels = mixedMoment B raw8685step0 raw8685step0Labels := by
      have hz : ∀ j, raw8685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8685step0 = (fun i j => raw8685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8685step0 raw8685; decide +kernel
      have hl : raw8685step0Labels = raw8685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8685 raw8685Labels permutation346 hz
    mixedMoment B raw8685step0 raw8685step0Labels = mixedMoment B raw8685step1 raw8685step1Labels := by
      have ha : raw8685step1 = (fun i j => raw8685step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8685step1 raw8685step0; decide +kernel
      have hl : raw8685step1Labels = raw8685step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8685step0 raw8685step0Labels permutation40 permutation3
    mixedMoment B raw8685step1 raw8685step1Labels = mixedMoment B raw8685step2 raw8685step2Labels := by
      have ha : raw8685step2 = raw8685step1 := by apply Matrix.ext; unfold raw8685step2 raw8685step1; decide +kernel
      have hl : raw8685step1Labels = labelEmbedding6 ∘ raw8685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8685step1 raw8685step1Labels raw8685step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw8686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8686step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8686 raw8686Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw8686 raw8686Labels = mixedMoment B raw8686step0 raw8686step0Labels := by
      have ha : raw8686step0 = (fun i j => raw8686 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8686step0 raw8686; decide +kernel
      have hl : raw8686step0Labels = raw8686Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8686 raw8686Labels permutation184 permutation3
    mixedMoment B raw8686step0 raw8686step0Labels = mixedMoment B raw8686step1 raw8686step1Labels := by
      have ha : raw8686step1 = raw8686step0 := by apply Matrix.ext; unfold raw8686step1 raw8686step0; decide +kernel
      have hl : raw8686step0Labels = labelEmbedding6 ∘ raw8686step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8686step0 raw8686step0Labels raw8686step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw8687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8687step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8687 raw8687Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw8687 raw8687Labels = mixedMoment B raw8687step0 raw8687step0Labels := by
      have hz : ∀ j, raw8687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8687step0 = (fun i j => raw8687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8687step0 raw8687; decide +kernel
      have hl : raw8687step0Labels = raw8687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8687 raw8687Labels permutation346 hz
    mixedMoment B raw8687step0 raw8687step0Labels = mixedMoment B raw8687step1 raw8687step1Labels := by
      have ha : raw8687step1 = (fun i j => raw8687step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8687step1 raw8687step0; decide +kernel
      have hl : raw8687step1Labels = raw8687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8687step0 raw8687step0Labels permutation40 permutation3
    mixedMoment B raw8687step1 raw8687step1Labels = mixedMoment B raw8687step2 raw8687step2Labels := by
      have ha : raw8687step2 = raw8687step1 := by apply Matrix.ext; unfold raw8687step2 raw8687step1; decide +kernel
      have hl : raw8687step1Labels = labelEmbedding6 ∘ raw8687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8687step1 raw8687step1Labels raw8687step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw8688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8688step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8688 raw8688Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw8688 raw8688Labels = mixedMoment B raw8688step0 raw8688step0Labels := by
      have hz : ∀ j, raw8688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8688step0 = (fun i j => raw8688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8688step0 raw8688; decide +kernel
      have hl : raw8688step0Labels = raw8688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8688 raw8688Labels permutation346 hz
    mixedMoment B raw8688step0 raw8688step0Labels = mixedMoment B raw8688step1 raw8688step1Labels := by
      have ha : raw8688step1 = (fun i j => raw8688step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8688step1 raw8688step0; decide +kernel
      have hl : raw8688step1Labels = raw8688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8688step0 raw8688step0Labels permutation46 permutation3
    mixedMoment B raw8688step1 raw8688step1Labels = mixedMoment B raw8688step2 raw8688step2Labels := by
      have ha : raw8688step2 = raw8688step1 := by apply Matrix.ext; unfold raw8688step2 raw8688step1; decide +kernel
      have hl : raw8688step1Labels = labelEmbedding6 ∘ raw8688step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8688step1 raw8688step1Labels raw8688step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw8689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8689step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8689 raw8689Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw8689 raw8689Labels = mixedMoment B raw8689step0 raw8689step0Labels := by
      have hz : ∀ j, raw8689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8689step0 = (fun i j => raw8689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8689step0 raw8689; decide +kernel
      have hl : raw8689step0Labels = raw8689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8689 raw8689Labels permutation346 hz
    mixedMoment B raw8689step0 raw8689step0Labels = mixedMoment B raw8689step1 raw8689step1Labels := by
      have ha : raw8689step1 = (fun i j => raw8689step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8689step1 raw8689step0; decide +kernel
      have hl : raw8689step1Labels = raw8689step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8689step0 raw8689step0Labels permutation43 permutation3
    mixedMoment B raw8689step1 raw8689step1Labels = mixedMoment B raw8689step2 raw8689step2Labels := by
      have ha : raw8689step2 = raw8689step1 := by apply Matrix.ext; unfold raw8689step2 raw8689step1; decide +kernel
      have hl : raw8689step1Labels = labelEmbedding6 ∘ raw8689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8689step1 raw8689step1Labels raw8689step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw8690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8690step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8690 raw8690Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw8690 raw8690Labels = mixedMoment B raw8690step0 raw8690step0Labels := by
      have hz : ∀ j, raw8690 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8690step0 = (fun i j => raw8690 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8690step0 raw8690; decide +kernel
      have hl : raw8690step0Labels = raw8690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8690 raw8690Labels permutation265 hz
    mixedMoment B raw8690step0 raw8690step0Labels = mixedMoment B raw8690step1 raw8690step1Labels := by
      have ha : raw8690step1 = (fun i j => raw8690step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8690step1 raw8690step0; decide +kernel
      have hl : raw8690step1Labels = raw8690step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8690step0 raw8690step0Labels permutation40 permutation3
    mixedMoment B raw8690step1 raw8690step1Labels = mixedMoment B raw8690step2 raw8690step2Labels := by
      have ha : raw8690step2 = raw8690step1 := by apply Matrix.ext; unfold raw8690step2 raw8690step1; decide +kernel
      have hl : raw8690step1Labels = labelEmbedding6 ∘ raw8690step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8690step1 raw8690step1Labels raw8690step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw8691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8691step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8691 raw8691Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw8691 raw8691Labels = mixedMoment B raw8691step0 raw8691step0Labels := by
      have ha : raw8691step0 = (fun i j => raw8691 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8691step0 raw8691; decide +kernel
      have hl : raw8691step0Labels = raw8691Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8691 raw8691Labels permutation160 permutation3
    mixedMoment B raw8691step0 raw8691step0Labels = mixedMoment B raw8691step1 raw8691step1Labels := by
      have ha : raw8691step1 = raw8691step0 := by apply Matrix.ext; unfold raw8691step1 raw8691step0; decide +kernel
      have hl : raw8691step0Labels = labelEmbedding6 ∘ raw8691step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8691step0 raw8691step0Labels raw8691step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw8692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8692step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8692step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8692 raw8692Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw8692 raw8692Labels = mixedMoment B raw8692step0 raw8692step0Labels := by
      have hz : ∀ j, raw8692 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8692step0 = (fun i j => raw8692 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8692step0 raw8692; decide +kernel
      have hl : raw8692step0Labels = raw8692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8692 raw8692Labels permutation265 hz
    mixedMoment B raw8692step0 raw8692step0Labels = mixedMoment B raw8692step1 raw8692step1Labels := by
      have ha : raw8692step1 = (fun i j => raw8692step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8692step1 raw8692step0; decide +kernel
      have hl : raw8692step1Labels = raw8692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8692step0 raw8692step0Labels permutation40 permutation3
    mixedMoment B raw8692step1 raw8692step1Labels = mixedMoment B raw8692step2 raw8692step2Labels := by
      have ha : raw8692step2 = raw8692step1 := by apply Matrix.ext; unfold raw8692step2 raw8692step1; decide +kernel
      have hl : raw8692step1Labels = labelEmbedding6 ∘ raw8692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8692step1 raw8692step1Labels raw8692step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw8693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8693step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8693 raw8693Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw8693 raw8693Labels = mixedMoment B raw8693step0 raw8693step0Labels := by
      have hz : ∀ j, raw8693 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8693step0 = (fun i j => raw8693 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8693step0 raw8693; decide +kernel
      have hl : raw8693step0Labels = raw8693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8693 raw8693Labels permutation265 hz
    mixedMoment B raw8693step0 raw8693step0Labels = mixedMoment B raw8693step1 raw8693step1Labels := by
      have ha : raw8693step1 = (fun i j => raw8693step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8693step1 raw8693step0; decide +kernel
      have hl : raw8693step1Labels = raw8693step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8693step0 raw8693step0Labels permutation46 permutation3
    mixedMoment B raw8693step1 raw8693step1Labels = mixedMoment B raw8693step2 raw8693step2Labels := by
      have ha : raw8693step2 = raw8693step1 := by apply Matrix.ext; unfold raw8693step2 raw8693step1; decide +kernel
      have hl : raw8693step1Labels = labelEmbedding6 ∘ raw8693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8693step1 raw8693step1Labels raw8693step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw8694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8694step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8694 raw8694Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw8694 raw8694Labels = mixedMoment B raw8694step0 raw8694step0Labels := by
      have hz : ∀ j, raw8694 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8694step0 = (fun i j => raw8694 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8694step0 raw8694; decide +kernel
      have hl : raw8694step0Labels = raw8694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8694 raw8694Labels permutation265 hz
    mixedMoment B raw8694step0 raw8694step0Labels = mixedMoment B raw8694step1 raw8694step1Labels := by
      have ha : raw8694step1 = (fun i j => raw8694step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8694step1 raw8694step0; decide +kernel
      have hl : raw8694step1Labels = raw8694step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8694step0 raw8694step0Labels permutation43 permutation3
    mixedMoment B raw8694step1 raw8694step1Labels = mixedMoment B raw8694step2 raw8694step2Labels := by
      have ha : raw8694step2 = raw8694step1 := by apply Matrix.ext; unfold raw8694step2 raw8694step1; decide +kernel
      have hl : raw8694step1Labels = labelEmbedding6 ∘ raw8694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8694step1 raw8694step1Labels raw8694step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw8695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8695step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8695 raw8695Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw8695 raw8695Labels = mixedMoment B raw8695step0 raw8695step0Labels := by
      have hz : ∀ j, raw8695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8695step0 = (fun i j => raw8695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8695step0 raw8695; decide +kernel
      have hl : raw8695step0Labels = raw8695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8695 raw8695Labels permutation346 hz
    mixedMoment B raw8695step0 raw8695step0Labels = mixedMoment B raw8695step1 raw8695step1Labels := by
      have hz : ∀ j, raw8695step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8695step1 = (fun i j => raw8695step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8695step1 raw8695step0; decide +kernel
      have hl : raw8695step1Labels = raw8695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8695step0 raw8695step0Labels permutation56 hz
    mixedMoment B raw8695step1 raw8695step1Labels = mixedMoment B raw8695step2 raw8695step2Labels := by
      have ha : raw8695step2 = (fun i j => raw8695step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8695step2 raw8695step1; decide +kernel
      have hl : raw8695step2Labels = raw8695step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8695step1 raw8695step1Labels permutation10 permutation3
    mixedMoment B raw8695step2 raw8695step2Labels = mixedMoment B raw8695step3 raw8695step3Labels := by
      have ha : raw8695step3 = raw8695step2 := by apply Matrix.ext; unfold raw8695step3 raw8695step2; decide +kernel
      have hl : raw8695step2Labels = labelEmbedding6 ∘ raw8695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8695step2 raw8695step2Labels raw8695step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw8696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8696step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8696 raw8696Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw8696 raw8696Labels = mixedMoment B raw8696step0 raw8696step0Labels := by
      have hz : ∀ j, raw8696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8696step0 = (fun i j => raw8696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8696step0 raw8696; decide +kernel
      have hl : raw8696step0Labels = raw8696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8696 raw8696Labels permutation346 hz
    mixedMoment B raw8696step0 raw8696step0Labels = mixedMoment B raw8696step1 raw8696step1Labels := by
      have ha : raw8696step1 = (fun i j => raw8696step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8696step1 raw8696step0; decide +kernel
      have hl : raw8696step1Labels = raw8696step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8696step0 raw8696step0Labels permutation34 permutation3
    mixedMoment B raw8696step1 raw8696step1Labels = mixedMoment B raw8696step2 raw8696step2Labels := by
      have ha : raw8696step2 = raw8696step1 := by apply Matrix.ext; unfold raw8696step2 raw8696step1; decide +kernel
      have hl : raw8696step1Labels = labelEmbedding6 ∘ raw8696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8696step1 raw8696step1Labels raw8696step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw8697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8697step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8697 raw8697Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw8697 raw8697Labels = mixedMoment B raw8697step0 raw8697step0Labels := by
      have hz : ∀ j, raw8697 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8697step0 = (fun i j => raw8697 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8697step0 raw8697; decide +kernel
      have hl : raw8697step0Labels = raw8697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8697 raw8697Labels permutation265 hz
    mixedMoment B raw8697step0 raw8697step0Labels = mixedMoment B raw8697step1 raw8697step1Labels := by
      have ha : raw8697step1 = (fun i j => raw8697step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8697step1 raw8697step0; decide +kernel
      have hl : raw8697step1Labels = raw8697step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8697step0 raw8697step0Labels permutation34 permutation3
    mixedMoment B raw8697step1 raw8697step1Labels = mixedMoment B raw8697step2 raw8697step2Labels := by
      have ha : raw8697step2 = raw8697step1 := by apply Matrix.ext; unfold raw8697step2 raw8697step1; decide +kernel
      have hl : raw8697step1Labels = labelEmbedding6 ∘ raw8697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8697step1 raw8697step1Labels raw8697step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw8698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8698step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8698 raw8698Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw8698 raw8698Labels = mixedMoment B raw8698step0 raw8698step0Labels := by
      have hz : ∀ j, raw8698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8698step0 = (fun i j => raw8698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8698step0 raw8698; decide +kernel
      have hl : raw8698step0Labels = raw8698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8698 raw8698Labels permutation346 hz
    mixedMoment B raw8698step0 raw8698step0Labels = mixedMoment B raw8698step1 raw8698step1Labels := by
      have hz : ∀ j, raw8698step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8698step1 = (fun i j => raw8698step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8698step1 raw8698step0; decide +kernel
      have hl : raw8698step1Labels = raw8698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8698step0 raw8698step0Labels permutation56 hz
    mixedMoment B raw8698step1 raw8698step1Labels = mixedMoment B raw8698step2 raw8698step2Labels := by
      have ha : raw8698step2 = (fun i j => raw8698step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8698step2 raw8698step1; decide +kernel
      have hl : raw8698step2Labels = raw8698step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8698step1 raw8698step1Labels permutation10 permutation3
    mixedMoment B raw8698step2 raw8698step2Labels = mixedMoment B raw8698step3 raw8698step3Labels := by
      have ha : raw8698step3 = raw8698step2 := by apply Matrix.ext; unfold raw8698step3 raw8698step2; decide +kernel
      have hl : raw8698step2Labels = labelEmbedding6 ∘ raw8698step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8698step2 raw8698step2Labels raw8698step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw8699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8699step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8699step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8699 raw8699Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw8699 raw8699Labels = mixedMoment B raw8699step0 raw8699step0Labels := by
      have hz : ∀ j, raw8699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8699step0 = (fun i j => raw8699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8699step0 raw8699; decide +kernel
      have hl : raw8699step0Labels = raw8699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8699 raw8699Labels permutation346 hz
    mixedMoment B raw8699step0 raw8699step0Labels = mixedMoment B raw8699step1 raw8699step1Labels := by
      have hz : ∀ j, raw8699step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8699step1 = (fun i j => raw8699step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8699step1 raw8699step0; decide +kernel
      have hl : raw8699step1Labels = raw8699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8699step0 raw8699step0Labels permutation56 hz
    mixedMoment B raw8699step1 raw8699step1Labels = mixedMoment B raw8699step2 raw8699step2Labels := by
      have ha : raw8699step2 = (fun i j => raw8699step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8699step2 raw8699step1; decide +kernel
      have hl : raw8699step2Labels = raw8699step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8699step1 raw8699step1Labels permutation17 permutation4
    mixedMoment B raw8699step2 raw8699step2Labels = mixedMoment B raw8699step3 raw8699step3Labels := by
      have ha : raw8699step3 = raw8699step2 := by apply Matrix.ext; unfold raw8699step3 raw8699step2; decide +kernel
      have hl : raw8699step2Labels = labelEmbedding7 ∘ raw8699step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8699step2 raw8699step2Labels raw8699step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw8700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8700step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8700step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8700step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8700 raw8700Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw8700 raw8700Labels = mixedMoment B raw8700step0 raw8700step0Labels := by
      have hz : ∀ j, raw8700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8700step0 = (fun i j => raw8700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8700step0 raw8700; decide +kernel
      have hl : raw8700step0Labels = raw8700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8700 raw8700Labels permutation346 hz
    mixedMoment B raw8700step0 raw8700step0Labels = mixedMoment B raw8700step1 raw8700step1Labels := by
      have hz : ∀ j, raw8700step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8700step1 = (fun i j => raw8700step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8700step1 raw8700step0; decide +kernel
      have hl : raw8700step1Labels = raw8700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8700step0 raw8700step0Labels permutation56 hz
    mixedMoment B raw8700step1 raw8700step1Labels = mixedMoment B raw8700step2 raw8700step2Labels := by
      have ha : raw8700step2 = (fun i j => raw8700step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8700step2 raw8700step1; decide +kernel
      have hl : raw8700step2Labels = raw8700step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8700step1 raw8700step1Labels permutation9 permutation3
    mixedMoment B raw8700step2 raw8700step2Labels = mixedMoment B raw8700step3 raw8700step3Labels := by
      have ha : raw8700step3 = raw8700step2 := by apply Matrix.ext; unfold raw8700step3 raw8700step2; decide +kernel
      have hl : raw8700step2Labels = labelEmbedding6 ∘ raw8700step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8700step2 raw8700step2Labels raw8700step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw8701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8701step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8701step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8701 raw8701Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw8701 raw8701Labels = mixedMoment B raw8701step0 raw8701step0Labels := by
      have hz : ∀ j, raw8701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8701step0 = (fun i j => raw8701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8701step0 raw8701; decide +kernel
      have hl : raw8701step0Labels = raw8701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8701 raw8701Labels permutation346 hz
    mixedMoment B raw8701step0 raw8701step0Labels = mixedMoment B raw8701step1 raw8701step1Labels := by
      have ha : raw8701step1 = (fun i j => raw8701step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8701step1 raw8701step0; decide +kernel
      have hl : raw8701step1Labels = raw8701step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8701step0 raw8701step0Labels permutation33 permutation3
    mixedMoment B raw8701step1 raw8701step1Labels = mixedMoment B raw8701step2 raw8701step2Labels := by
      have ha : raw8701step2 = raw8701step1 := by apply Matrix.ext; unfold raw8701step2 raw8701step1; decide +kernel
      have hl : raw8701step1Labels = labelEmbedding6 ∘ raw8701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8701step1 raw8701step1Labels raw8701step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw8702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8702step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8702 raw8702Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw8702 raw8702Labels = mixedMoment B raw8702step0 raw8702step0Labels := by
      have hz : ∀ j, raw8702 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8702step0 = (fun i j => raw8702 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8702step0 raw8702; decide +kernel
      have hl : raw8702step0Labels = raw8702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8702 raw8702Labels permutation265 hz
    mixedMoment B raw8702step0 raw8702step0Labels = mixedMoment B raw8702step1 raw8702step1Labels := by
      have ha : raw8702step1 = (fun i j => raw8702step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8702step1 raw8702step0; decide +kernel
      have hl : raw8702step1Labels = raw8702step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8702step0 raw8702step0Labels permutation33 permutation3
    mixedMoment B raw8702step1 raw8702step1Labels = mixedMoment B raw8702step2 raw8702step2Labels := by
      have ha : raw8702step2 = raw8702step1 := by apply Matrix.ext; unfold raw8702step2 raw8702step1; decide +kernel
      have hl : raw8702step1Labels = labelEmbedding6 ∘ raw8702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8702step1 raw8702step1Labels raw8702step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw8703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8703step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8703step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8703step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8703 raw8703Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw8703 raw8703Labels = mixedMoment B raw8703step0 raw8703step0Labels := by
      have hz : ∀ j, raw8703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8703step0 = (fun i j => raw8703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8703step0 raw8703; decide +kernel
      have hl : raw8703step0Labels = raw8703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8703 raw8703Labels permutation346 hz
    mixedMoment B raw8703step0 raw8703step0Labels = mixedMoment B raw8703step1 raw8703step1Labels := by
      have hz : ∀ j, raw8703step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8703step1 = (fun i j => raw8703step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8703step1 raw8703step0; decide +kernel
      have hl : raw8703step1Labels = raw8703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8703step0 raw8703step0Labels permutation56 hz
    mixedMoment B raw8703step1 raw8703step1Labels = mixedMoment B raw8703step2 raw8703step2Labels := by
      have ha : raw8703step2 = (fun i j => raw8703step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8703step2 raw8703step1; decide +kernel
      have hl : raw8703step2Labels = raw8703step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8703step1 raw8703step1Labels permutation9 permutation3
    mixedMoment B raw8703step2 raw8703step2Labels = mixedMoment B raw8703step3 raw8703step3Labels := by
      have ha : raw8703step3 = raw8703step2 := by apply Matrix.ext; unfold raw8703step3 raw8703step2; decide +kernel
      have hl : raw8703step2Labels = labelEmbedding6 ∘ raw8703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8703step2 raw8703step2Labels raw8703step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
