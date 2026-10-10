import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23680 raw23680Labels = mixedMoment B node703 node703Labels := by
  calc
    mixedMoment B raw23680 raw23680Labels = mixedMoment B raw23680step0 raw23680step0Labels := by
      have ha : raw23680step0 = (fun i j => raw23680 (permutation207 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23680step0 raw23680; decide +kernel
      have hl : raw23680step0Labels = raw23680Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23680 raw23680Labels permutation207 permutation2
    _ = mixedMoment B node703 node703Labels := by rfl

def raw23681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw23681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23681 raw23681Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw23681 raw23681Labels = mixedMoment B raw23681step0 raw23681step0Labels := by
      have hz : ∀ j, raw23681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23681step0 = (fun i j => raw23681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23681step0 raw23681; decide +kernel
      have hl : raw23681step0Labels = raw23681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23681 raw23681Labels permutation434 hz
    mixedMoment B raw23681step0 raw23681step0Labels = mixedMoment B raw23681step1 raw23681step1Labels := by
      have ha : raw23681step1 = (fun i j => raw23681step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23681step1 raw23681step0; decide +kernel
      have hl : raw23681step1Labels = raw23681step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23681step0 raw23681step0Labels permutation42 permutation2
    _ = mixedMoment B node806 node806Labels := by rfl

def raw23682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23682 raw23682Labels = mixedMoment B node552 node552Labels := by
  calc
    mixedMoment B raw23682 raw23682Labels = mixedMoment B raw23682step0 raw23682step0Labels := by
      have hz : ∀ j, raw23682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23682step0 = (fun i j => raw23682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23682step0 raw23682; decide +kernel
      have hl : raw23682step0Labels = raw23682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23682 raw23682Labels permutation434 hz
    mixedMoment B raw23682step0 raw23682step0Labels = mixedMoment B raw23682step1 raw23682step1Labels := by
      have ha : raw23682step1 = (fun i j => raw23682step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23682step1 raw23682step0; decide +kernel
      have hl : raw23682step1Labels = raw23682step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23682step0 raw23682step0Labels permutation33 permutation4
    mixedMoment B raw23682step1 raw23682step1Labels = mixedMoment B raw23682step2 raw23682step2Labels := by
      have ha : raw23682step2 = -raw23682step1 := by apply Matrix.ext; change ∀ i j, raw23682step2 i j = -(raw23682step1 i j); unfold raw23682step2 raw23682step1; decide +kernel
      have hl : raw23682step2Labels = raw23682step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node552 node552Labels := by rfl

def raw23683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23683step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23683 raw23683Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw23683 raw23683Labels = mixedMoment B raw23683step0 raw23683step0Labels := by
      have hz : ∀ j, raw23683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23683step0 = (fun i j => raw23683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23683step0 raw23683; decide +kernel
      have hl : raw23683step0Labels = raw23683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23683 raw23683Labels permutation434 hz
    mixedMoment B raw23683step0 raw23683step0Labels = mixedMoment B raw23683step1 raw23683step1Labels := by
      have hz : ∀ j, raw23683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23683step1 = (fun i j => raw23683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23683step1 raw23683step0; decide +kernel
      have hl : raw23683step1Labels = raw23683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23683step0 raw23683step0Labels permutation56 hz
    mixedMoment B raw23683step1 raw23683step1Labels = mixedMoment B raw23683step2 raw23683step2Labels := by
      have ha : raw23683step2 = (fun i j => raw23683step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23683step2 raw23683step1; decide +kernel
      have hl : raw23683step2Labels = raw23683step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23683step1 raw23683step1Labels permutation9 permutation4
    mixedMoment B raw23683step2 raw23683step2Labels = mixedMoment B raw23683step3 raw23683step3Labels := by
      have ha : raw23683step3 = -raw23683step2 := by apply Matrix.ext; change ∀ i j, raw23683step3 i j = -(raw23683step2 i j); unfold raw23683step3 raw23683step2; decide +kernel
      have hl : raw23683step3Labels = raw23683step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node852 node852Labels := by rfl

def raw23684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23684 raw23684Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw23684 raw23684Labels = mixedMoment B raw23684step0 raw23684step0Labels := by
      have hz : ∀ j, raw23684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23684step0 = (fun i j => raw23684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23684step0 raw23684; decide +kernel
      have hl : raw23684step0Labels = raw23684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23684 raw23684Labels permutation434 hz
    mixedMoment B raw23684step0 raw23684step0Labels = mixedMoment B raw23684step1 raw23684step1Labels := by
      have ha : raw23684step1 = (fun i j => raw23684step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23684step1 raw23684step0; decide +kernel
      have hl : raw23684step1Labels = raw23684step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23684step0 raw23684step0Labels permutation32 permutation4
    mixedMoment B raw23684step1 raw23684step1Labels = mixedMoment B raw23684step2 raw23684step2Labels := by
      have ha : raw23684step2 = -raw23684step1 := by apply Matrix.ext; change ∀ i j, raw23684step2 i j = -(raw23684step1 i j); unfold raw23684step2 raw23684step1; decide +kernel
      have hl : raw23684step2Labels = raw23684step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node848 node848Labels := by rfl

def raw23685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23685 raw23685Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw23685 raw23685Labels = mixedMoment B raw23685step0 raw23685step0Labels := by
      have hz : ∀ j, raw23685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23685step0 = (fun i j => raw23685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23685step0 raw23685; decide +kernel
      have hl : raw23685step0Labels = raw23685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23685 raw23685Labels permutation434 hz
    mixedMoment B raw23685step0 raw23685step0Labels = mixedMoment B raw23685step1 raw23685step1Labels := by
      have ha : raw23685step1 = (fun i j => raw23685step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23685step1 raw23685step0; decide +kernel
      have hl : raw23685step1Labels = raw23685step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23685step0 raw23685step0Labels permutation50 permutation4
    mixedMoment B raw23685step1 raw23685step1Labels = mixedMoment B raw23685step2 raw23685step2Labels := by
      have ha : raw23685step2 = -raw23685step1 := by apply Matrix.ext; change ∀ i j, raw23685step2 i j = -(raw23685step1 i j); unfold raw23685step2 raw23685step1; decide +kernel
      have hl : raw23685step2Labels = raw23685step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node823 node823Labels := by rfl

def raw23686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23686 raw23686Labels = mixedMoment B node1641 node1641Labels := by
  calc
    mixedMoment B raw23686 raw23686Labels = mixedMoment B raw23686step0 raw23686step0Labels := by
      have hz : ∀ j, raw23686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23686step0 = (fun i j => raw23686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23686step0 raw23686; decide +kernel
      have hl : raw23686step0Labels = raw23686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23686 raw23686Labels permutation434 hz
    _ = mixedMoment B node1641 node1641Labels := by rfl

def raw23687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23687 raw23687Labels = mixedMoment B node1641 node1641Labels := by
  calc
    mixedMoment B raw23687 raw23687Labels = mixedMoment B raw23687step0 raw23687step0Labels := by
      have hz : ∀ j, raw23687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23687step0 = (fun i j => raw23687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23687step0 raw23687; decide +kernel
      have hl : raw23687step0Labels = raw23687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23687 raw23687Labels permutation434 hz
    mixedMoment B raw23687step0 raw23687step0Labels = mixedMoment B raw23687step1 raw23687step1Labels := by
      have ha : raw23687step1 = (fun i j => raw23687step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23687step1 raw23687step0; decide +kernel
      have hl : raw23687step1Labels = raw23687step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23687step0 raw23687step0Labels permutation38 permutation2
    _ = mixedMoment B node1641 node1641Labels := by rfl

def raw23688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23688 raw23688Labels = mixedMoment B node1595 node1595Labels := by
  calc
    mixedMoment B raw23688 raw23688Labels = mixedMoment B raw23688step0 raw23688step0Labels := by
      have ha : raw23688step0 = (fun i j => raw23688 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23688step0 raw23688; decide +kernel
      have hl : raw23688step0Labels = raw23688Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23688 raw23688Labels permutation200 permutation2
    _ = mixedMoment B node1595 node1595Labels := by rfl

def raw23689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23689 raw23689Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw23689 raw23689Labels = mixedMoment B raw23689step0 raw23689step0Labels := by
      have hz : ∀ j, raw23689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23689step0 = (fun i j => raw23689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23689step0 raw23689; decide +kernel
      have hl : raw23689step0Labels = raw23689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23689 raw23689Labels permutation434 hz
    mixedMoment B raw23689step0 raw23689step0Labels = mixedMoment B raw23689step1 raw23689step1Labels := by
      have ha : raw23689step1 = (fun i j => raw23689step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23689step1 raw23689step0; decide +kernel
      have hl : raw23689step1Labels = raw23689step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23689step0 raw23689step0Labels permutation33 permutation2
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw23690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23690 raw23690Labels = mixedMoment B node544 node544Labels := by
  calc
    mixedMoment B raw23690 raw23690Labels = mixedMoment B raw23690step0 raw23690step0Labels := by
      have hz : ∀ j, raw23690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23690step0 = (fun i j => raw23690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23690step0 raw23690; decide +kernel
      have hl : raw23690step0Labels = raw23690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23690 raw23690Labels permutation434 hz
    mixedMoment B raw23690step0 raw23690step0Labels = mixedMoment B raw23690step1 raw23690step1Labels := by
      have ha : raw23690step1 = (fun i j => raw23690step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23690step1 raw23690step0; decide +kernel
      have hl : raw23690step1Labels = raw23690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23690step0 raw23690step0Labels permutation38 permutation2
    _ = mixedMoment B node544 node544Labels := by rfl

def raw23691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23691 raw23691Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw23691 raw23691Labels = mixedMoment B raw23691step0 raw23691step0Labels := by
      have hz : ∀ j, raw23691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23691step0 = (fun i j => raw23691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23691step0 raw23691; decide +kernel
      have hl : raw23691step0Labels = raw23691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23691 raw23691Labels permutation434 hz
    mixedMoment B raw23691step0 raw23691step0Labels = mixedMoment B raw23691step1 raw23691step1Labels := by
      have ha : raw23691step1 = (fun i j => raw23691step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23691step1 raw23691step0; decide +kernel
      have hl : raw23691step1Labels = raw23691step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23691step0 raw23691step0Labels permutation38 permutation2
    _ = mixedMoment B node739 node739Labels := by rfl

def raw23692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23692 raw23692Labels = mixedMoment B node704 node704Labels := by
  calc
    mixedMoment B raw23692 raw23692Labels = mixedMoment B raw23692step0 raw23692step0Labels := by
      have ha : raw23692step0 = (fun i j => raw23692 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23692step0 raw23692; decide +kernel
      have hl : raw23692step0Labels = raw23692Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23692 raw23692Labels permutation206 permutation2
    _ = mixedMoment B node704 node704Labels := by rfl

def raw23693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23693 raw23693Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw23693 raw23693Labels = mixedMoment B raw23693step0 raw23693step0Labels := by
      have hz : ∀ j, raw23693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23693step0 = (fun i j => raw23693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23693step0 raw23693; decide +kernel
      have hl : raw23693step0Labels = raw23693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23693 raw23693Labels permutation434 hz
    mixedMoment B raw23693step0 raw23693step0Labels = mixedMoment B raw23693step1 raw23693step1Labels := by
      have ha : raw23693step1 = (fun i j => raw23693step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23693step1 raw23693step0; decide +kernel
      have hl : raw23693step1Labels = raw23693step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23693step0 raw23693step0Labels permutation39 permutation2
    _ = mixedMoment B node810 node810Labels := by rfl

def raw23694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23694step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23694step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23694step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23694step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23694 raw23694Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw23694 raw23694Labels = mixedMoment B raw23694step0 raw23694step0Labels := by
      have hz : ∀ j, raw23694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23694step0 = (fun i j => raw23694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23694step0 raw23694; decide +kernel
      have hl : raw23694step0Labels = raw23694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23694 raw23694Labels permutation434 hz
    mixedMoment B raw23694step0 raw23694step0Labels = mixedMoment B raw23694step1 raw23694step1Labels := by
      have hz : ∀ j, raw23694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23694step1 = (fun i j => raw23694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23694step1 raw23694step0; decide +kernel
      have hl : raw23694step1Labels = raw23694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23694step0 raw23694step0Labels permutation80 hz
    mixedMoment B raw23694step1 raw23694step1Labels = mixedMoment B raw23694step2 raw23694step2Labels := by
      have ha : raw23694step2 = (fun i j => raw23694step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23694step2 raw23694step1; decide +kernel
      have hl : raw23694step2Labels = raw23694step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23694step1 raw23694step1Labels permutation9 permutation7
    mixedMoment B raw23694step2 raw23694step2Labels = mixedMoment B raw23694step3 raw23694step3Labels := by
      have ha : raw23694step3 = -raw23694step2 := by apply Matrix.ext; change ∀ i j, raw23694step3 i j = -(raw23694step2 i j); unfold raw23694step3 raw23694step2; decide +kernel
      have hl : raw23694step3Labels = raw23694step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23694step3 raw23694step3Labels = mixedMoment B raw23694step4 raw23694step4Labels := by
      have ha : raw23694step4 = raw23694step3 := by apply Matrix.ext; unfold raw23694step4 raw23694step3; decide +kernel
      have hl : raw23694step3Labels = labelEmbedding10 ∘ raw23694step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23694step3 raw23694step3Labels raw23694step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw23695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23695step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23695step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23695step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23695 raw23695Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23695 raw23695Labels = mixedMoment B raw23695step0 raw23695step0Labels := by
      have hz : ∀ j, raw23695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23695step0 = (fun i j => raw23695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23695step0 raw23695; decide +kernel
      have hl : raw23695step0Labels = raw23695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23695 raw23695Labels permutation434 hz
    mixedMoment B raw23695step0 raw23695step0Labels = mixedMoment B raw23695step1 raw23695step1Labels := by
      have ha : raw23695step1 = (fun i j => raw23695step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23695step1 raw23695step0; decide +kernel
      have hl : raw23695step1Labels = raw23695step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23695step0 raw23695step0Labels permutation39 permutation7
    mixedMoment B raw23695step1 raw23695step1Labels = mixedMoment B raw23695step2 raw23695step2Labels := by
      have ha : raw23695step2 = -raw23695step1 := by apply Matrix.ext; change ∀ i j, raw23695step2 i j = -(raw23695step1 i j); unfold raw23695step2 raw23695step1; decide +kernel
      have hl : raw23695step2Labels = raw23695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23695step2 raw23695step2Labels = mixedMoment B raw23695step3 raw23695step3Labels := by
      have ha : raw23695step3 = raw23695step2 := by apply Matrix.ext; unfold raw23695step3 raw23695step2; decide +kernel
      have hl : raw23695step2Labels = labelEmbedding10 ∘ raw23695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23695step2 raw23695step2Labels raw23695step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw23696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23696step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23696step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23696step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23696step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23696 raw23696Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23696 raw23696Labels = mixedMoment B raw23696step0 raw23696step0Labels := by
      have hz : ∀ j, raw23696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23696step0 = (fun i j => raw23696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23696step0 raw23696; decide +kernel
      have hl : raw23696step0Labels = raw23696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23696 raw23696Labels permutation346 hz
    mixedMoment B raw23696step0 raw23696step0Labels = mixedMoment B raw23696step1 raw23696step1Labels := by
      have ha : raw23696step1 = (fun i j => raw23696step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23696step1 raw23696step0; decide +kernel
      have hl : raw23696step1Labels = raw23696step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23696step0 raw23696step0Labels permutation39 permutation7
    mixedMoment B raw23696step1 raw23696step1Labels = mixedMoment B raw23696step2 raw23696step2Labels := by
      have ha : raw23696step2 = -raw23696step1 := by apply Matrix.ext; change ∀ i j, raw23696step2 i j = -(raw23696step1 i j); unfold raw23696step2 raw23696step1; decide +kernel
      have hl : raw23696step2Labels = raw23696step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23696step2 raw23696step2Labels = mixedMoment B raw23696step3 raw23696step3Labels := by
      have ha : raw23696step3 = raw23696step2 := by apply Matrix.ext; unfold raw23696step3 raw23696step2; decide +kernel
      have hl : raw23696step2Labels = labelEmbedding10 ∘ raw23696step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23696step2 raw23696step2Labels raw23696step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw23697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23697step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23697step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23697step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23697 raw23697Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw23697 raw23697Labels = mixedMoment B raw23697step0 raw23697step0Labels := by
      have hz : ∀ j, raw23697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23697step0 = (fun i j => raw23697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23697step0 raw23697; decide +kernel
      have hl : raw23697step0Labels = raw23697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23697 raw23697Labels permutation434 hz
    mixedMoment B raw23697step0 raw23697step0Labels = mixedMoment B raw23697step1 raw23697step1Labels := by
      have hz : ∀ j, raw23697step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23697step1 = (fun i j => raw23697step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23697step1 raw23697step0; decide +kernel
      have hl : raw23697step1Labels = raw23697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23697step0 raw23697step0Labels permutation80 hz
    mixedMoment B raw23697step1 raw23697step1Labels = mixedMoment B raw23697step2 raw23697step2Labels := by
      have ha : raw23697step2 = (fun i j => raw23697step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23697step2 raw23697step1; decide +kernel
      have hl : raw23697step2Labels = raw23697step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23697step1 raw23697step1Labels permutation9 permutation7
    mixedMoment B raw23697step2 raw23697step2Labels = mixedMoment B raw23697step3 raw23697step3Labels := by
      have ha : raw23697step3 = -raw23697step2 := by apply Matrix.ext; change ∀ i j, raw23697step3 i j = -(raw23697step2 i j); unfold raw23697step3 raw23697step2; decide +kernel
      have hl : raw23697step3Labels = raw23697step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23697step3 raw23697step3Labels = mixedMoment B raw23697step4 raw23697step4Labels := by
      have ha : raw23697step4 = raw23697step3 := by apply Matrix.ext; unfold raw23697step4 raw23697step3; decide +kernel
      have hl : raw23697step3Labels = labelEmbedding10 ∘ raw23697step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23697step3 raw23697step3Labels raw23697step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw23698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23698step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23698step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23698step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23698step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23698 raw23698Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw23698 raw23698Labels = mixedMoment B raw23698step0 raw23698step0Labels := by
      have hz : ∀ j, raw23698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23698step0 = (fun i j => raw23698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23698step0 raw23698; decide +kernel
      have hl : raw23698step0Labels = raw23698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23698 raw23698Labels permutation434 hz
    mixedMoment B raw23698step0 raw23698step0Labels = mixedMoment B raw23698step1 raw23698step1Labels := by
      have hz : ∀ j, raw23698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23698step1 = (fun i j => raw23698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23698step1 raw23698step0; decide +kernel
      have hl : raw23698step1Labels = raw23698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23698step0 raw23698step0Labels permutation80 hz
    mixedMoment B raw23698step1 raw23698step1Labels = mixedMoment B raw23698step2 raw23698step2Labels := by
      have ha : raw23698step2 = (fun i j => raw23698step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23698step2 raw23698step1; decide +kernel
      have hl : raw23698step2Labels = raw23698step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23698step1 raw23698step1Labels permutation9 permutation7
    mixedMoment B raw23698step2 raw23698step2Labels = mixedMoment B raw23698step3 raw23698step3Labels := by
      have ha : raw23698step3 = -raw23698step2 := by apply Matrix.ext; change ∀ i j, raw23698step3 i j = -(raw23698step2 i j); unfold raw23698step3 raw23698step2; decide +kernel
      have hl : raw23698step3Labels = raw23698step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23698step3 raw23698step3Labels = mixedMoment B raw23698step4 raw23698step4Labels := by
      have ha : raw23698step4 = raw23698step3 := by apply Matrix.ext; unfold raw23698step4 raw23698step3; decide +kernel
      have hl : raw23698step3Labels = labelEmbedding10 ∘ raw23698step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23698step3 raw23698step3Labels raw23698step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw23699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23699 raw23699Labels = mixedMoment B node4130 node4130Labels := by
  calc
    mixedMoment B raw23699 raw23699Labels = mixedMoment B raw23699step0 raw23699step0Labels := by
      have hz : ∀ j, raw23699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23699step0 = (fun i j => raw23699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23699step0 raw23699; decide +kernel
      have hl : raw23699step0Labels = raw23699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23699 raw23699Labels permutation434 hz
    mixedMoment B raw23699step0 raw23699step0Labels = mixedMoment B raw23699step1 raw23699step1Labels := by
      have hz : ∀ j, raw23699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23699step1 = (fun i j => raw23699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23699step1 raw23699step0; decide +kernel
      have hl : raw23699step1Labels = raw23699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23699step0 raw23699step0Labels permutation80 hz
    mixedMoment B raw23699step1 raw23699step1Labels = mixedMoment B raw23699step2 raw23699step2Labels := by
      have ha : raw23699step2 = (fun i j => raw23699step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23699step2 raw23699step1; decide +kernel
      have hl : raw23699step2Labels = raw23699step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23699step1 raw23699step1Labels permutation9 permutation2
    _ = mixedMoment B node4130 node4130Labels := by rfl

def raw23700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23700 raw23700Labels = mixedMoment B node4221 node4221Labels := by
  calc
    mixedMoment B raw23700 raw23700Labels = mixedMoment B raw23700step0 raw23700step0Labels := by
      have hz : ∀ j, raw23700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23700step0 = (fun i j => raw23700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23700step0 raw23700; decide +kernel
      have hl : raw23700step0Labels = raw23700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23700 raw23700Labels permutation434 hz
    mixedMoment B raw23700step0 raw23700step0Labels = mixedMoment B raw23700step1 raw23700step1Labels := by
      have ha : raw23700step1 = (fun i j => raw23700step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23700step1 raw23700step0; decide +kernel
      have hl : raw23700step1Labels = raw23700step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23700step0 raw23700step0Labels permutation39 permutation2
    _ = mixedMoment B node4221 node4221Labels := by rfl

def raw23701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23701 raw23701Labels = mixedMoment B node4221 node4221Labels := by
  calc
    mixedMoment B raw23701 raw23701Labels = mixedMoment B raw23701step0 raw23701step0Labels := by
      have hz : ∀ j, raw23701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23701step0 = (fun i j => raw23701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23701step0 raw23701; decide +kernel
      have hl : raw23701step0Labels = raw23701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23701 raw23701Labels permutation346 hz
    mixedMoment B raw23701step0 raw23701step0Labels = mixedMoment B raw23701step1 raw23701step1Labels := by
      have ha : raw23701step1 = (fun i j => raw23701step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23701step1 raw23701step0; decide +kernel
      have hl : raw23701step1Labels = raw23701step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23701step0 raw23701step0Labels permutation39 permutation2
    _ = mixedMoment B node4221 node4221Labels := by rfl

def raw23702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23702 raw23702Labels = mixedMoment B node4283 node4283Labels := by
  calc
    mixedMoment B raw23702 raw23702Labels = mixedMoment B raw23702step0 raw23702step0Labels := by
      have hz : ∀ j, raw23702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23702step0 = (fun i j => raw23702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23702step0 raw23702; decide +kernel
      have hl : raw23702step0Labels = raw23702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23702 raw23702Labels permutation434 hz
    mixedMoment B raw23702step0 raw23702step0Labels = mixedMoment B raw23702step1 raw23702step1Labels := by
      have hz : ∀ j, raw23702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23702step1 = (fun i j => raw23702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23702step1 raw23702step0; decide +kernel
      have hl : raw23702step1Labels = raw23702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23702step0 raw23702step0Labels permutation80 hz
    _ = mixedMoment B node4283 node4283Labels := by rfl

def raw23703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23703step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23703step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw23703step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23703step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw23703step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23703step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23703 raw23703Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23703 raw23703Labels = mixedMoment B raw23703step0 raw23703step0Labels := by
      have hz : ∀ j, raw23703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23703step0 = (fun i j => raw23703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23703step0 raw23703; decide +kernel
      have hl : raw23703step0Labels = raw23703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23703 raw23703Labels permutation434 hz
    mixedMoment B raw23703step0 raw23703step0Labels = mixedMoment B raw23703step1 raw23703step1Labels := by
      have hz : ∀ j, raw23703step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23703step1 = (fun i j => raw23703step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23703step1 raw23703step0; decide +kernel
      have hl : raw23703step1Labels = raw23703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23703step0 raw23703step0Labels permutation80 hz
    mixedMoment B raw23703step1 raw23703step1Labels = mixedMoment B raw23703step2 raw23703step2Labels := by
      have hz : ∀ i, raw23703step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw23703step2 = (fun i j => raw23703step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw23703step2 raw23703step1; decide +kernel
      have hl : raw23703step2Labels = (fun j => raw23703step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23703step1 raw23703step1Labels permutation4 hz
    mixedMoment B raw23703step2 raw23703step2Labels = mixedMoment B raw23703step3 raw23703step3Labels := by
      have ha : raw23703step3 = (fun i j => raw23703step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23703step3 raw23703step2; decide +kernel
      have hl : raw23703step3Labels = raw23703step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23703step2 raw23703step2Labels permutation9 permutation0
    mixedMoment B raw23703step3 raw23703step3Labels = mixedMoment B raw23703step4 raw23703step4Labels := by
      have ha : raw23703step4 = raw23703step3 := by apply Matrix.ext; unfold raw23703step4 raw23703step3; decide +kernel
      have hl : raw23703step3Labels = labelEmbedding2 ∘ raw23703step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23703step3 raw23703step3Labels raw23703step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw23704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23704 raw23704Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw23704 raw23704Labels = mixedMoment B raw23704step0 raw23704step0Labels := by
      have hz : ∀ j, raw23704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23704step0 = (fun i j => raw23704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23704step0 raw23704; decide +kernel
      have hl : raw23704step0Labels = raw23704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23704 raw23704Labels permutation434 hz
    mixedMoment B raw23704step0 raw23704step0Labels = mixedMoment B raw23704step1 raw23704step1Labels := by
      have ha : raw23704step1 = (fun i j => raw23704step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23704step1 raw23704step0; decide +kernel
      have hl : raw23704step1Labels = raw23704step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23704step0 raw23704step0Labels permutation33 permutation2
    _ = mixedMoment B node4102 node4102Labels := by rfl

def raw23705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23705 raw23705Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw23705 raw23705Labels = mixedMoment B raw23705step0 raw23705step0Labels := by
      have hz : ∀ j, raw23705 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23705step0 = (fun i j => raw23705 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23705step0 raw23705; decide +kernel
      have hl : raw23705step0Labels = raw23705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23705 raw23705Labels permutation434 hz
    mixedMoment B raw23705step0 raw23705step0Labels = mixedMoment B raw23705step1 raw23705step1Labels := by
      have ha : raw23705step1 = (fun i j => raw23705step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23705step1 raw23705step0; decide +kernel
      have hl : raw23705step1Labels = raw23705step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23705step0 raw23705step0Labels permutation33 permutation2
    _ = mixedMoment B node4234 node4234Labels := by rfl

def raw23706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23706 raw23706Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw23706 raw23706Labels = mixedMoment B raw23706step0 raw23706step0Labels := by
      have ha : raw23706step0 = (fun i j => raw23706 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23706step0 raw23706; decide +kernel
      have hl : raw23706step0Labels = raw23706Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23706 raw23706Labels permutation201 permutation2
    _ = mixedMoment B node4197 node4197Labels := by rfl

def raw23707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23707 raw23707Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw23707 raw23707Labels = mixedMoment B raw23707step0 raw23707step0Labels := by
      have hz : ∀ j, raw23707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23707step0 = (fun i j => raw23707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23707step0 raw23707; decide +kernel
      have hl : raw23707step0Labels = raw23707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23707 raw23707Labels permutation434 hz
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw23708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23708 raw23708Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw23708 raw23708Labels = mixedMoment B raw23708step0 raw23708step0Labels := by
      have hz : ∀ j, raw23708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23708step0 = (fun i j => raw23708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23708step0 raw23708; decide +kernel
      have hl : raw23708step0Labels = raw23708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23708 raw23708Labels permutation434 hz
    mixedMoment B raw23708step0 raw23708step0Labels = mixedMoment B raw23708step1 raw23708step1Labels := by
      have ha : raw23708step1 = (fun i j => raw23708step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23708step1 raw23708step0; decide +kernel
      have hl : raw23708step1Labels = raw23708step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23708step0 raw23708step0Labels permutation33 permutation2
    _ = mixedMoment B node4264 node4264Labels := by rfl

def raw23709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23709 raw23709Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw23709 raw23709Labels = mixedMoment B raw23709step0 raw23709step0Labels := by
      have hz : ∀ j, raw23709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23709step0 = (fun i j => raw23709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23709step0 raw23709; decide +kernel
      have hl : raw23709step0Labels = raw23709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23709 raw23709Labels permutation346 hz
    mixedMoment B raw23709step0 raw23709step0Labels = mixedMoment B raw23709step1 raw23709step1Labels := by
      have ha : raw23709step1 = (fun i j => raw23709step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23709step1 raw23709step0; decide +kernel
      have hl : raw23709step1Labels = raw23709step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23709step0 raw23709step0Labels permutation33 permutation2
    _ = mixedMoment B node4102 node4102Labels := by rfl

def raw23710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23710 raw23710Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw23710 raw23710Labels = mixedMoment B raw23710step0 raw23710step0Labels := by
      have hz : ∀ j, raw23710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23710step0 = (fun i j => raw23710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23710step0 raw23710; decide +kernel
      have hl : raw23710step0Labels = raw23710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23710 raw23710Labels permutation346 hz
    mixedMoment B raw23710step0 raw23710step0Labels = mixedMoment B raw23710step1 raw23710step1Labels := by
      have ha : raw23710step1 = (fun i j => raw23710step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23710step1 raw23710step0; decide +kernel
      have hl : raw23710step1Labels = raw23710step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23710step0 raw23710step0Labels permutation33 permutation2
    _ = mixedMoment B node4234 node4234Labels := by rfl

def raw23711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23711 raw23711Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw23711 raw23711Labels = mixedMoment B raw23711step0 raw23711step0Labels := by
      have ha : raw23711step0 = (fun i j => raw23711 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23711step0 raw23711; decide +kernel
      have hl : raw23711step0Labels = raw23711Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23711 raw23711Labels permutation177 permutation2
    _ = mixedMoment B node4197 node4197Labels := by rfl

def raw23712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23712 raw23712Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw23712 raw23712Labels = mixedMoment B raw23712step0 raw23712step0Labels := by
      have hz : ∀ j, raw23712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23712step0 = (fun i j => raw23712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23712step0 raw23712; decide +kernel
      have hl : raw23712step0Labels = raw23712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23712 raw23712Labels permutation346 hz
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw23713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23713 raw23713Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw23713 raw23713Labels = mixedMoment B raw23713step0 raw23713step0Labels := by
      have hz : ∀ j, raw23713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23713step0 = (fun i j => raw23713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23713step0 raw23713; decide +kernel
      have hl : raw23713step0Labels = raw23713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23713 raw23713Labels permutation346 hz
    mixedMoment B raw23713step0 raw23713step0Labels = mixedMoment B raw23713step1 raw23713step1Labels := by
      have ha : raw23713step1 = (fun i j => raw23713step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23713step1 raw23713step0; decide +kernel
      have hl : raw23713step1Labels = raw23713step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23713step0 raw23713step0Labels permutation33 permutation2
    _ = mixedMoment B node4264 node4264Labels := by rfl

def raw23714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23714step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23714 raw23714Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw23714 raw23714Labels = mixedMoment B raw23714step0 raw23714step0Labels := by
      have hz : ∀ j, raw23714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23714step0 = (fun i j => raw23714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23714step0 raw23714; decide +kernel
      have hl : raw23714step0Labels = raw23714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23714 raw23714Labels permutation434 hz
    mixedMoment B raw23714step0 raw23714step0Labels = mixedMoment B raw23714step1 raw23714step1Labels := by
      have hz : ∀ j, raw23714step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23714step1 = (fun i j => raw23714step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23714step1 raw23714step0; decide +kernel
      have hl : raw23714step1Labels = raw23714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23714step0 raw23714step0Labels permutation80 hz
    mixedMoment B raw23714step1 raw23714step1Labels = mixedMoment B raw23714step2 raw23714step2Labels := by
      have ha : raw23714step2 = (fun i j => raw23714step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23714step2 raw23714step1; decide +kernel
      have hl : raw23714step2Labels = raw23714step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23714step1 raw23714step1Labels permutation9 permutation2
    _ = mixedMoment B node4110 node4110Labels := by rfl

def raw23715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23715step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23715 raw23715Labels = mixedMoment B node4242 node4242Labels := by
  calc
    mixedMoment B raw23715 raw23715Labels = mixedMoment B raw23715step0 raw23715step0Labels := by
      have hz : ∀ j, raw23715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23715step0 = (fun i j => raw23715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23715step0 raw23715; decide +kernel
      have hl : raw23715step0Labels = raw23715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23715 raw23715Labels permutation434 hz
    mixedMoment B raw23715step0 raw23715step0Labels = mixedMoment B raw23715step1 raw23715step1Labels := by
      have hz : ∀ j, raw23715step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23715step1 = (fun i j => raw23715step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23715step1 raw23715step0; decide +kernel
      have hl : raw23715step1Labels = raw23715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23715step0 raw23715step0Labels permutation80 hz
    mixedMoment B raw23715step1 raw23715step1Labels = mixedMoment B raw23715step2 raw23715step2Labels := by
      have ha : raw23715step2 = (fun i j => raw23715step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23715step2 raw23715step1; decide +kernel
      have hl : raw23715step2Labels = raw23715step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23715step1 raw23715step1Labels permutation9 permutation2
    _ = mixedMoment B node4242 node4242Labels := by rfl

def raw23716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23716 raw23716Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw23716 raw23716Labels = mixedMoment B raw23716step0 raw23716step0Labels := by
      have hz : ∀ j, raw23716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23716step0 = (fun i j => raw23716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23716step0 raw23716; decide +kernel
      have hl : raw23716step0Labels = raw23716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23716 raw23716Labels permutation434 hz
    mixedMoment B raw23716step0 raw23716step0Labels = mixedMoment B raw23716step1 raw23716step1Labels := by
      have ha : raw23716step1 = (fun i j => raw23716step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23716step1 raw23716step0; decide +kernel
      have hl : raw23716step1Labels = raw23716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23716step0 raw23716step0Labels permutation39 permutation2
    _ = mixedMoment B node4204 node4204Labels := by rfl

def raw23717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23717 raw23717Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw23717 raw23717Labels = mixedMoment B raw23717step0 raw23717step0Labels := by
      have hz : ∀ j, raw23717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23717step0 = (fun i j => raw23717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23717step0 raw23717; decide +kernel
      have hl : raw23717step0Labels = raw23717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23717 raw23717Labels permutation346 hz
    mixedMoment B raw23717step0 raw23717step0Labels = mixedMoment B raw23717step1 raw23717step1Labels := by
      have ha : raw23717step1 = (fun i j => raw23717step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23717step1 raw23717step0; decide +kernel
      have hl : raw23717step1Labels = raw23717step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23717step0 raw23717step0Labels permutation39 permutation2
    _ = mixedMoment B node4204 node4204Labels := by rfl

def raw23718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![3, -1, -2], ![1, 0, -1]]
def raw23718step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23718step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw23718step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23718 raw23718Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw23718 raw23718Labels = mixedMoment B raw23718step0 raw23718step0Labels := by
      have hz : ∀ j, raw23718 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23718step0 = (fun i j => raw23718 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23718step0 raw23718; decide +kernel
      have hl : raw23718step0Labels = raw23718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23718 raw23718Labels permutation434 hz
    mixedMoment B raw23718step0 raw23718step0Labels = mixedMoment B raw23718step1 raw23718step1Labels := by
      have hz : ∀ j, raw23718step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23718step1 = (fun i j => raw23718step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23718step1 raw23718step0; decide +kernel
      have hl : raw23718step1Labels = raw23718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23718step0 raw23718step0Labels permutation80 hz
    mixedMoment B raw23718step1 raw23718step1Labels = mixedMoment B raw23718step2 raw23718step2Labels := by
      have ha : raw23718step2 = (fun i j => raw23718step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23718step2 raw23718step1; decide +kernel
      have hl : raw23718step2Labels = raw23718step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23718step1 raw23718step1Labels permutation9 permutation2
    _ = mixedMoment B node4269 node4269Labels := by rfl

def raw23719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23719 raw23719Labels = mixedMoment B node4111 node4111Labels := by
  calc
    mixedMoment B raw23719 raw23719Labels = mixedMoment B raw23719step0 raw23719step0Labels := by
      have hz : ∀ j, raw23719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23719step0 = (fun i j => raw23719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23719step0 raw23719; decide +kernel
      have hl : raw23719step0Labels = raw23719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23719 raw23719Labels permutation434 hz
    mixedMoment B raw23719step0 raw23719step0Labels = mixedMoment B raw23719step1 raw23719step1Labels := by
      have hz : ∀ j, raw23719step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23719step1 = (fun i j => raw23719step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23719step1 raw23719step0; decide +kernel
      have hl : raw23719step1Labels = raw23719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23719step0 raw23719step0Labels permutation80 hz
    _ = mixedMoment B node4111 node4111Labels := by rfl

def raw23720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23720 raw23720Labels = mixedMoment B node4243 node4243Labels := by
  calc
    mixedMoment B raw23720 raw23720Labels = mixedMoment B raw23720step0 raw23720step0Labels := by
      have hz : ∀ j, raw23720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23720step0 = (fun i j => raw23720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23720step0 raw23720; decide +kernel
      have hl : raw23720step0Labels = raw23720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23720 raw23720Labels permutation434 hz
    mixedMoment B raw23720step0 raw23720step0Labels = mixedMoment B raw23720step1 raw23720step1Labels := by
      have hz : ∀ j, raw23720step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23720step1 = (fun i j => raw23720step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23720step1 raw23720step0; decide +kernel
      have hl : raw23720step1Labels = raw23720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23720step0 raw23720step0Labels permutation80 hz
    _ = mixedMoment B node4243 node4243Labels := by rfl

def raw23721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23721 raw23721Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw23721 raw23721Labels = mixedMoment B raw23721step0 raw23721step0Labels := by
      have hz : ∀ j, raw23721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23721step0 = (fun i j => raw23721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23721step0 raw23721; decide +kernel
      have hl : raw23721step0Labels = raw23721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23721 raw23721Labels permutation434 hz
    mixedMoment B raw23721step0 raw23721step0Labels = mixedMoment B raw23721step1 raw23721step1Labels := by
      have ha : raw23721step1 = (fun i j => raw23721step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23721step1 raw23721step0; decide +kernel
      have hl : raw23721step1Labels = raw23721step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23721step0 raw23721step0Labels permutation38 permutation2
    _ = mixedMoment B node4205 node4205Labels := by rfl

def raw23722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23722 raw23722Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw23722 raw23722Labels = mixedMoment B raw23722step0 raw23722step0Labels := by
      have hz : ∀ j, raw23722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23722step0 = (fun i j => raw23722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23722step0 raw23722; decide +kernel
      have hl : raw23722step0Labels = raw23722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23722 raw23722Labels permutation346 hz
    mixedMoment B raw23722step0 raw23722step0Labels = mixedMoment B raw23722step1 raw23722step1Labels := by
      have ha : raw23722step1 = (fun i j => raw23722step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23722step1 raw23722step0; decide +kernel
      have hl : raw23722step1Labels = raw23722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23722step0 raw23722step0Labels permutation38 permutation2
    _ = mixedMoment B node4205 node4205Labels := by rfl

def raw23723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw23723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23723 raw23723Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw23723 raw23723Labels = mixedMoment B raw23723step0 raw23723step0Labels := by
      have hz : ∀ j, raw23723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23723step0 = (fun i j => raw23723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23723step0 raw23723; decide +kernel
      have hl : raw23723step0Labels = raw23723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23723 raw23723Labels permutation434 hz
    mixedMoment B raw23723step0 raw23723step0Labels = mixedMoment B raw23723step1 raw23723step1Labels := by
      have hz : ∀ j, raw23723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23723step1 = (fun i j => raw23723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23723step1 raw23723step0; decide +kernel
      have hl : raw23723step1Labels = raw23723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23723step0 raw23723step0Labels permutation80 hz
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw23724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23724step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23724step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23724step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23724step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23724step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23724 raw23724Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw23724 raw23724Labels = mixedMoment B raw23724step0 raw23724step0Labels := by
      have hz : ∀ j, raw23724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23724step0 = (fun i j => raw23724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23724step0 raw23724; decide +kernel
      have hl : raw23724step0Labels = raw23724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23724 raw23724Labels permutation434 hz
    mixedMoment B raw23724step0 raw23724step0Labels = mixedMoment B raw23724step1 raw23724step1Labels := by
      have hz : ∀ j, raw23724step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23724step1 = (fun i j => raw23724step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23724step1 raw23724step0; decide +kernel
      have hl : raw23724step1Labels = raw23724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23724step0 raw23724step0Labels permutation80 hz
    mixedMoment B raw23724step1 raw23724step1Labels = mixedMoment B raw23724step2 raw23724step2Labels := by
      have ha : raw23724step2 = (fun i j => raw23724step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23724step2 raw23724step1; decide +kernel
      have hl : raw23724step2Labels = raw23724step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23724step1 raw23724step1Labels permutation9 permutation7
    mixedMoment B raw23724step2 raw23724step2Labels = mixedMoment B raw23724step3 raw23724step3Labels := by
      have ha : raw23724step3 = -raw23724step2 := by apply Matrix.ext; change ∀ i j, raw23724step3 i j = -(raw23724step2 i j); unfold raw23724step3 raw23724step2; decide +kernel
      have hl : raw23724step3Labels = raw23724step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23724step3 raw23724step3Labels = mixedMoment B raw23724step4 raw23724step4Labels := by
      have ha : raw23724step4 = raw23724step3 := by apply Matrix.ext; unfold raw23724step4 raw23724step3; decide +kernel
      have hl : raw23724step3Labels = labelEmbedding1 ∘ raw23724step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23724step3 raw23724step3Labels raw23724step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw23725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23725 raw23725Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw23725 raw23725Labels = mixedMoment B raw23725step0 raw23725step0Labels := by
      have hz : ∀ j, raw23725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23725step0 = (fun i j => raw23725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23725step0 raw23725; decide +kernel
      have hl : raw23725step0Labels = raw23725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23725 raw23725Labels permutation434 hz
    mixedMoment B raw23725step0 raw23725step0Labels = mixedMoment B raw23725step1 raw23725step1Labels := by
      have ha : raw23725step1 = (fun i j => raw23725step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23725step1 raw23725step0; decide +kernel
      have hl : raw23725step1Labels = raw23725step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23725step0 raw23725step0Labels permutation39 permutation7
    mixedMoment B raw23725step1 raw23725step1Labels = mixedMoment B raw23725step2 raw23725step2Labels := by
      have ha : raw23725step2 = -raw23725step1 := by apply Matrix.ext; change ∀ i j, raw23725step2 i j = -(raw23725step1 i j); unfold raw23725step2 raw23725step1; decide +kernel
      have hl : raw23725step2Labels = raw23725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23725step2 raw23725step2Labels = mixedMoment B raw23725step3 raw23725step3Labels := by
      have ha : raw23725step3 = raw23725step2 := by apply Matrix.ext; unfold raw23725step3 raw23725step2; decide +kernel
      have hl : raw23725step2Labels = labelEmbedding1 ∘ raw23725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23725step2 raw23725step2Labels raw23725step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw23726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23726step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23726 raw23726Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw23726 raw23726Labels = mixedMoment B raw23726step0 raw23726step0Labels := by
      have hz : ∀ j, raw23726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23726step0 = (fun i j => raw23726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23726step0 raw23726; decide +kernel
      have hl : raw23726step0Labels = raw23726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23726 raw23726Labels permutation346 hz
    mixedMoment B raw23726step0 raw23726step0Labels = mixedMoment B raw23726step1 raw23726step1Labels := by
      have ha : raw23726step1 = (fun i j => raw23726step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23726step1 raw23726step0; decide +kernel
      have hl : raw23726step1Labels = raw23726step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23726step0 raw23726step0Labels permutation39 permutation7
    mixedMoment B raw23726step1 raw23726step1Labels = mixedMoment B raw23726step2 raw23726step2Labels := by
      have ha : raw23726step2 = -raw23726step1 := by apply Matrix.ext; change ∀ i j, raw23726step2 i j = -(raw23726step1 i j); unfold raw23726step2 raw23726step1; decide +kernel
      have hl : raw23726step2Labels = raw23726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23726step2 raw23726step2Labels = mixedMoment B raw23726step3 raw23726step3Labels := by
      have ha : raw23726step3 = raw23726step2 := by apply Matrix.ext; unfold raw23726step3 raw23726step2; decide +kernel
      have hl : raw23726step2Labels = labelEmbedding1 ∘ raw23726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23726step2 raw23726step2Labels raw23726step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw23727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23727step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23727step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23727 raw23727Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw23727 raw23727Labels = mixedMoment B raw23727step0 raw23727step0Labels := by
      have hz : ∀ j, raw23727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23727step0 = (fun i j => raw23727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23727step0 raw23727; decide +kernel
      have hl : raw23727step0Labels = raw23727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23727 raw23727Labels permutation434 hz
    mixedMoment B raw23727step0 raw23727step0Labels = mixedMoment B raw23727step1 raw23727step1Labels := by
      have hz : ∀ j, raw23727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23727step1 = (fun i j => raw23727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23727step1 raw23727step0; decide +kernel
      have hl : raw23727step1Labels = raw23727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23727step0 raw23727step0Labels permutation80 hz
    mixedMoment B raw23727step1 raw23727step1Labels = mixedMoment B raw23727step2 raw23727step2Labels := by
      have ha : raw23727step2 = (fun i j => raw23727step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23727step2 raw23727step1; decide +kernel
      have hl : raw23727step2Labels = raw23727step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23727step1 raw23727step1Labels permutation9 permutation7
    mixedMoment B raw23727step2 raw23727step2Labels = mixedMoment B raw23727step3 raw23727step3Labels := by
      have ha : raw23727step3 = -raw23727step2 := by apply Matrix.ext; change ∀ i j, raw23727step3 i j = -(raw23727step2 i j); unfold raw23727step3 raw23727step2; decide +kernel
      have hl : raw23727step3Labels = raw23727step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23727step3 raw23727step3Labels = mixedMoment B raw23727step4 raw23727step4Labels := by
      have ha : raw23727step4 = raw23727step3 := by apply Matrix.ext; unfold raw23727step4 raw23727step3; decide +kernel
      have hl : raw23727step3Labels = labelEmbedding1 ∘ raw23727step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23727step3 raw23727step3Labels raw23727step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw23728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23728step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23728 raw23728Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw23728 raw23728Labels = mixedMoment B raw23728step0 raw23728step0Labels := by
      have hz : ∀ j, raw23728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23728step0 = (fun i j => raw23728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23728step0 raw23728; decide +kernel
      have hl : raw23728step0Labels = raw23728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23728 raw23728Labels permutation434 hz
    mixedMoment B raw23728step0 raw23728step0Labels = mixedMoment B raw23728step1 raw23728step1Labels := by
      have hz : ∀ j, raw23728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23728step1 = (fun i j => raw23728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23728step1 raw23728step0; decide +kernel
      have hl : raw23728step1Labels = raw23728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23728step0 raw23728step0Labels permutation80 hz
    mixedMoment B raw23728step1 raw23728step1Labels = mixedMoment B raw23728step2 raw23728step2Labels := by
      have ha : raw23728step2 = (fun i j => raw23728step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23728step2 raw23728step1; decide +kernel
      have hl : raw23728step2Labels = raw23728step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23728step1 raw23728step1Labels permutation9 permutation7
    mixedMoment B raw23728step2 raw23728step2Labels = mixedMoment B raw23728step3 raw23728step3Labels := by
      have ha : raw23728step3 = -raw23728step2 := by apply Matrix.ext; change ∀ i j, raw23728step3 i j = -(raw23728step2 i j); unfold raw23728step3 raw23728step2; decide +kernel
      have hl : raw23728step3Labels = raw23728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23728step3 raw23728step3Labels = mixedMoment B raw23728step4 raw23728step4Labels := by
      have ha : raw23728step4 = raw23728step3 := by apply Matrix.ext; unfold raw23728step4 raw23728step3; decide +kernel
      have hl : raw23728step3Labels = labelEmbedding1 ∘ raw23728step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23728step3 raw23728step3Labels raw23728step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1082 node1082Labels := by rfl

def raw23729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23729step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23729step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23729step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23729step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23729step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23729 raw23729Labels = mixedMoment B node689 node689Labels := by
  calc
    mixedMoment B raw23729 raw23729Labels = mixedMoment B raw23729step0 raw23729step0Labels := by
      have hz : ∀ j, raw23729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23729step0 = (fun i j => raw23729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23729step0 raw23729; decide +kernel
      have hl : raw23729step0Labels = raw23729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23729 raw23729Labels permutation434 hz
    mixedMoment B raw23729step0 raw23729step0Labels = mixedMoment B raw23729step1 raw23729step1Labels := by
      have hz : ∀ j, raw23729step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23729step1 = (fun i j => raw23729step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23729step1 raw23729step0; decide +kernel
      have hl : raw23729step1Labels = raw23729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23729step0 raw23729step0Labels permutation80 hz
    mixedMoment B raw23729step1 raw23729step1Labels = mixedMoment B raw23729step2 raw23729step2Labels := by
      have ha : raw23729step2 = (fun i j => raw23729step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23729step2 raw23729step1; decide +kernel
      have hl : raw23729step2Labels = raw23729step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23729step1 raw23729step1Labels permutation9 permutation7
    mixedMoment B raw23729step2 raw23729step2Labels = mixedMoment B raw23729step3 raw23729step3Labels := by
      have ha : raw23729step3 = -raw23729step2 := by apply Matrix.ext; change ∀ i j, raw23729step3 i j = -(raw23729step2 i j); unfold raw23729step3 raw23729step2; decide +kernel
      have hl : raw23729step3Labels = raw23729step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23729step3 raw23729step3Labels = mixedMoment B raw23729step4 raw23729step4Labels := by
      have ha : raw23729step4 = raw23729step3 := by apply Matrix.ext; unfold raw23729step4 raw23729step3; decide +kernel
      have hl : raw23729step3Labels = labelEmbedding1 ∘ raw23729step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23729step3 raw23729step3Labels raw23729step4Labels labelEmbedding1 hl
    _ = mixedMoment B node689 node689Labels := by rfl

def raw23730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23730 raw23730Labels = mixedMoment B node768 node768Labels := by
  calc
    mixedMoment B raw23730 raw23730Labels = mixedMoment B raw23730step0 raw23730step0Labels := by
      have hz : ∀ j, raw23730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23730step0 = (fun i j => raw23730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23730step0 raw23730; decide +kernel
      have hl : raw23730step0Labels = raw23730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23730 raw23730Labels permutation434 hz
    mixedMoment B raw23730step0 raw23730step0Labels = mixedMoment B raw23730step1 raw23730step1Labels := by
      have ha : raw23730step1 = (fun i j => raw23730step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23730step1 raw23730step0; decide +kernel
      have hl : raw23730step1Labels = raw23730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23730step0 raw23730step0Labels permutation39 permutation7
    mixedMoment B raw23730step1 raw23730step1Labels = mixedMoment B raw23730step2 raw23730step2Labels := by
      have ha : raw23730step2 = -raw23730step1 := by apply Matrix.ext; change ∀ i j, raw23730step2 i j = -(raw23730step1 i j); unfold raw23730step2 raw23730step1; decide +kernel
      have hl : raw23730step2Labels = raw23730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23730step2 raw23730step2Labels = mixedMoment B raw23730step3 raw23730step3Labels := by
      have ha : raw23730step3 = raw23730step2 := by apply Matrix.ext; unfold raw23730step3 raw23730step2; decide +kernel
      have hl : raw23730step2Labels = labelEmbedding1 ∘ raw23730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23730step2 raw23730step2Labels raw23730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node768 node768Labels := by rfl

def raw23731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23731step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23731step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23731 raw23731Labels = mixedMoment B node768 node768Labels := by
  calc
    mixedMoment B raw23731 raw23731Labels = mixedMoment B raw23731step0 raw23731step0Labels := by
      have hz : ∀ j, raw23731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23731step0 = (fun i j => raw23731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23731step0 raw23731; decide +kernel
      have hl : raw23731step0Labels = raw23731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23731 raw23731Labels permutation346 hz
    mixedMoment B raw23731step0 raw23731step0Labels = mixedMoment B raw23731step1 raw23731step1Labels := by
      have ha : raw23731step1 = (fun i j => raw23731step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23731step1 raw23731step0; decide +kernel
      have hl : raw23731step1Labels = raw23731step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23731step0 raw23731step0Labels permutation39 permutation7
    mixedMoment B raw23731step1 raw23731step1Labels = mixedMoment B raw23731step2 raw23731step2Labels := by
      have ha : raw23731step2 = -raw23731step1 := by apply Matrix.ext; change ∀ i j, raw23731step2 i j = -(raw23731step1 i j); unfold raw23731step2 raw23731step1; decide +kernel
      have hl : raw23731step2Labels = raw23731step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23731step2 raw23731step2Labels = mixedMoment B raw23731step3 raw23731step3Labels := by
      have ha : raw23731step3 = raw23731step2 := by apply Matrix.ext; unfold raw23731step3 raw23731step2; decide +kernel
      have hl : raw23731step2Labels = labelEmbedding1 ∘ raw23731step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23731step2 raw23731step2Labels raw23731step3Labels labelEmbedding1 hl
    _ = mixedMoment B node768 node768Labels := by rfl

def raw23732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23732step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23732step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23732step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23732step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23732step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23732 raw23732Labels = mixedMoment B node856 node856Labels := by
  calc
    mixedMoment B raw23732 raw23732Labels = mixedMoment B raw23732step0 raw23732step0Labels := by
      have hz : ∀ j, raw23732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23732step0 = (fun i j => raw23732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23732step0 raw23732; decide +kernel
      have hl : raw23732step0Labels = raw23732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23732 raw23732Labels permutation434 hz
    mixedMoment B raw23732step0 raw23732step0Labels = mixedMoment B raw23732step1 raw23732step1Labels := by
      have hz : ∀ j, raw23732step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23732step1 = (fun i j => raw23732step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23732step1 raw23732step0; decide +kernel
      have hl : raw23732step1Labels = raw23732step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23732step0 raw23732step0Labels permutation80 hz
    mixedMoment B raw23732step1 raw23732step1Labels = mixedMoment B raw23732step2 raw23732step2Labels := by
      have ha : raw23732step2 = (fun i j => raw23732step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23732step2 raw23732step1; decide +kernel
      have hl : raw23732step2Labels = raw23732step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23732step1 raw23732step1Labels permutation9 permutation7
    mixedMoment B raw23732step2 raw23732step2Labels = mixedMoment B raw23732step3 raw23732step3Labels := by
      have ha : raw23732step3 = -raw23732step2 := by apply Matrix.ext; change ∀ i j, raw23732step3 i j = -(raw23732step2 i j); unfold raw23732step3 raw23732step2; decide +kernel
      have hl : raw23732step3Labels = raw23732step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23732step3 raw23732step3Labels = mixedMoment B raw23732step4 raw23732step4Labels := by
      have ha : raw23732step4 = raw23732step3 := by apply Matrix.ext; unfold raw23732step4 raw23732step3; decide +kernel
      have hl : raw23732step3Labels = labelEmbedding1 ∘ raw23732step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23732step3 raw23732step3Labels raw23732step4Labels labelEmbedding1 hl
    _ = mixedMoment B node856 node856Labels := by rfl

def raw23733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23733step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23733step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23733step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23733step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23733 raw23733Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23733 raw23733Labels = mixedMoment B raw23733step0 raw23733step0Labels := by
      have hz : ∀ j, raw23733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23733step0 = (fun i j => raw23733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23733step0 raw23733; decide +kernel
      have hl : raw23733step0Labels = raw23733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23733 raw23733Labels permutation434 hz
    mixedMoment B raw23733step0 raw23733step0Labels = mixedMoment B raw23733step1 raw23733step1Labels := by
      have hz : ∀ j, raw23733step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23733step1 = (fun i j => raw23733step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23733step1 raw23733step0; decide +kernel
      have hl : raw23733step1Labels = raw23733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23733step0 raw23733step0Labels permutation80 hz
    mixedMoment B raw23733step1 raw23733step1Labels = mixedMoment B raw23733step2 raw23733step2Labels := by
      have hz : ∀ i, raw23733step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw23733step2 = (fun i j => raw23733step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw23733step2 raw23733step1; decide +kernel
      have hl : raw23733step2Labels = (fun j => raw23733step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23733step1 raw23733step1Labels permutation4 hz
    mixedMoment B raw23733step2 raw23733step2Labels = mixedMoment B raw23733step3 raw23733step3Labels := by
      have ha : raw23733step3 = (fun i j => raw23733step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23733step3 raw23733step2; decide +kernel
      have hl : raw23733step3Labels = raw23733step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23733step2 raw23733step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw23734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23734 raw23734Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw23734 raw23734Labels = mixedMoment B raw23734step0 raw23734step0Labels := by
      have hz : ∀ j, raw23734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23734step0 = (fun i j => raw23734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23734step0 raw23734; decide +kernel
      have hl : raw23734step0Labels = raw23734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23734 raw23734Labels permutation434 hz
    mixedMoment B raw23734step0 raw23734step0Labels = mixedMoment B raw23734step1 raw23734step1Labels := by
      have ha : raw23734step1 = (fun i j => raw23734step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23734step1 raw23734step0; decide +kernel
      have hl : raw23734step1Labels = raw23734step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23734step0 raw23734step0Labels permutation39 permutation7
    mixedMoment B raw23734step1 raw23734step1Labels = mixedMoment B raw23734step2 raw23734step2Labels := by
      have ha : raw23734step2 = -raw23734step1 := by apply Matrix.ext; change ∀ i j, raw23734step2 i j = -(raw23734step1 i j); unfold raw23734step2 raw23734step1; decide +kernel
      have hl : raw23734step2Labels = raw23734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23734step2 raw23734step2Labels = mixedMoment B raw23734step3 raw23734step3Labels := by
      have ha : raw23734step3 = raw23734step2 := by apply Matrix.ext; unfold raw23734step3 raw23734step2; decide +kernel
      have hl : raw23734step2Labels = labelEmbedding1 ∘ raw23734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23734step2 raw23734step2Labels raw23734step3Labels labelEmbedding1 hl
    _ = mixedMoment B node664 node664Labels := by rfl

def raw23735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23735 raw23735Labels = mixedMoment B node800 node800Labels := by
  calc
    mixedMoment B raw23735 raw23735Labels = mixedMoment B raw23735step0 raw23735step0Labels := by
      have hz : ∀ j, raw23735 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23735step0 = (fun i j => raw23735 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23735step0 raw23735; decide +kernel
      have hl : raw23735step0Labels = raw23735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23735 raw23735Labels permutation434 hz
    mixedMoment B raw23735step0 raw23735step0Labels = mixedMoment B raw23735step1 raw23735step1Labels := by
      have ha : raw23735step1 = (fun i j => raw23735step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23735step1 raw23735step0; decide +kernel
      have hl : raw23735step1Labels = raw23735step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23735step0 raw23735step0Labels permutation39 permutation7
    mixedMoment B raw23735step1 raw23735step1Labels = mixedMoment B raw23735step2 raw23735step2Labels := by
      have ha : raw23735step2 = -raw23735step1 := by apply Matrix.ext; change ∀ i j, raw23735step2 i j = -(raw23735step1 i j); unfold raw23735step2 raw23735step1; decide +kernel
      have hl : raw23735step2Labels = raw23735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23735step2 raw23735step2Labels = mixedMoment B raw23735step3 raw23735step3Labels := by
      have ha : raw23735step3 = raw23735step2 := by apply Matrix.ext; unfold raw23735step3 raw23735step2; decide +kernel
      have hl : raw23735step2Labels = labelEmbedding1 ∘ raw23735step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23735step2 raw23735step2Labels raw23735step3Labels labelEmbedding1 hl
    _ = mixedMoment B node800 node800Labels := by rfl

def raw23736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23736 raw23736Labels = mixedMoment B node749 node749Labels := by
  calc
    mixedMoment B raw23736 raw23736Labels = mixedMoment B raw23736step0 raw23736step0Labels := by
      have ha : raw23736step0 = (fun i j => raw23736 (permutation207 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23736step0 raw23736; decide +kernel
      have hl : raw23736step0Labels = raw23736Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23736 raw23736Labels permutation207 permutation7
    mixedMoment B raw23736step0 raw23736step0Labels = mixedMoment B raw23736step1 raw23736step1Labels := by
      have ha : raw23736step1 = -raw23736step0 := by apply Matrix.ext; change ∀ i j, raw23736step1 i j = -(raw23736step0 i j); unfold raw23736step1 raw23736step0; decide +kernel
      have hl : raw23736step1Labels = raw23736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23736step1 raw23736step1Labels = mixedMoment B raw23736step2 raw23736step2Labels := by
      have ha : raw23736step2 = raw23736step1 := by apply Matrix.ext; unfold raw23736step2 raw23736step1; decide +kernel
      have hl : raw23736step1Labels = labelEmbedding1 ∘ raw23736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23736step1 raw23736step1Labels raw23736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node749 node749Labels := by rfl

def raw23737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23737 raw23737Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw23737 raw23737Labels = mixedMoment B raw23737step0 raw23737step0Labels := by
      have hz : ∀ j, raw23737 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23737step0 = (fun i j => raw23737 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23737step0 raw23737; decide +kernel
      have hl : raw23737step0Labels = raw23737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23737 raw23737Labels permutation434 hz
    mixedMoment B raw23737step0 raw23737step0Labels = mixedMoment B raw23737step1 raw23737step1Labels := by
      have ha : raw23737step1 = (fun i j => raw23737step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23737step1 raw23737step0; decide +kernel
      have hl : raw23737step1Labels = raw23737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23737step0 raw23737step0Labels permutation39 permutation7
    mixedMoment B raw23737step1 raw23737step1Labels = mixedMoment B raw23737step2 raw23737step2Labels := by
      have ha : raw23737step2 = -raw23737step1 := by apply Matrix.ext; change ∀ i j, raw23737step2 i j = -(raw23737step1 i j); unfold raw23737step2 raw23737step1; decide +kernel
      have hl : raw23737step2Labels = raw23737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23737step2 raw23737step2Labels = mixedMoment B raw23737step3 raw23737step3Labels := by
      have ha : raw23737step3 = raw23737step2 := by apply Matrix.ext; unfold raw23737step3 raw23737step2; decide +kernel
      have hl : raw23737step2Labels = labelEmbedding1 ∘ raw23737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23737step2 raw23737step2Labels raw23737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node807 node807Labels := by rfl

def raw23738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23738 raw23738Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw23738 raw23738Labels = mixedMoment B raw23738step0 raw23738step0Labels := by
      have hz : ∀ j, raw23738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23738step0 = (fun i j => raw23738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23738step0 raw23738; decide +kernel
      have hl : raw23738step0Labels = raw23738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23738 raw23738Labels permutation434 hz
    mixedMoment B raw23738step0 raw23738step0Labels = mixedMoment B raw23738step1 raw23738step1Labels := by
      have ha : raw23738step1 = (fun i j => raw23738step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23738step1 raw23738step0; decide +kernel
      have hl : raw23738step1Labels = raw23738step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23738step0 raw23738step0Labels permutation39 permutation7
    mixedMoment B raw23738step1 raw23738step1Labels = mixedMoment B raw23738step2 raw23738step2Labels := by
      have ha : raw23738step2 = -raw23738step1 := by apply Matrix.ext; change ∀ i j, raw23738step2 i j = -(raw23738step1 i j); unfold raw23738step2 raw23738step1; decide +kernel
      have hl : raw23738step2Labels = raw23738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23738step2 raw23738step2Labels = mixedMoment B raw23738step3 raw23738step3Labels := by
      have ha : raw23738step3 = raw23738step2 := by apply Matrix.ext; unfold raw23738step3 raw23738step2; decide +kernel
      have hl : raw23738step2Labels = labelEmbedding1 ∘ raw23738step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23738step2 raw23738step2Labels raw23738step3Labels labelEmbedding1 hl
    _ = mixedMoment B node806 node806Labels := by rfl

def raw23739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23739 raw23739Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw23739 raw23739Labels = mixedMoment B raw23739step0 raw23739step0Labels := by
      have hz : ∀ j, raw23739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23739step0 = (fun i j => raw23739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23739step0 raw23739; decide +kernel
      have hl : raw23739step0Labels = raw23739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23739 raw23739Labels permutation346 hz
    mixedMoment B raw23739step0 raw23739step0Labels = mixedMoment B raw23739step1 raw23739step1Labels := by
      have ha : raw23739step1 = (fun i j => raw23739step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23739step1 raw23739step0; decide +kernel
      have hl : raw23739step1Labels = raw23739step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23739step0 raw23739step0Labels permutation39 permutation7
    mixedMoment B raw23739step1 raw23739step1Labels = mixedMoment B raw23739step2 raw23739step2Labels := by
      have ha : raw23739step2 = -raw23739step1 := by apply Matrix.ext; change ∀ i j, raw23739step2 i j = -(raw23739step1 i j); unfold raw23739step2 raw23739step1; decide +kernel
      have hl : raw23739step2Labels = raw23739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23739step2 raw23739step2Labels = mixedMoment B raw23739step3 raw23739step3Labels := by
      have ha : raw23739step3 = raw23739step2 := by apply Matrix.ext; unfold raw23739step3 raw23739step2; decide +kernel
      have hl : raw23739step2Labels = labelEmbedding1 ∘ raw23739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23739step2 raw23739step2Labels raw23739step3Labels labelEmbedding1 hl
    _ = mixedMoment B node664 node664Labels := by rfl

def raw23740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23740step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23740 raw23740Labels = mixedMoment B node800 node800Labels := by
  calc
    mixedMoment B raw23740 raw23740Labels = mixedMoment B raw23740step0 raw23740step0Labels := by
      have hz : ∀ j, raw23740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23740step0 = (fun i j => raw23740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23740step0 raw23740; decide +kernel
      have hl : raw23740step0Labels = raw23740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23740 raw23740Labels permutation346 hz
    mixedMoment B raw23740step0 raw23740step0Labels = mixedMoment B raw23740step1 raw23740step1Labels := by
      have ha : raw23740step1 = (fun i j => raw23740step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23740step1 raw23740step0; decide +kernel
      have hl : raw23740step1Labels = raw23740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23740step0 raw23740step0Labels permutation39 permutation7
    mixedMoment B raw23740step1 raw23740step1Labels = mixedMoment B raw23740step2 raw23740step2Labels := by
      have ha : raw23740step2 = -raw23740step1 := by apply Matrix.ext; change ∀ i j, raw23740step2 i j = -(raw23740step1 i j); unfold raw23740step2 raw23740step1; decide +kernel
      have hl : raw23740step2Labels = raw23740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23740step2 raw23740step2Labels = mixedMoment B raw23740step3 raw23740step3Labels := by
      have ha : raw23740step3 = raw23740step2 := by apply Matrix.ext; unfold raw23740step3 raw23740step2; decide +kernel
      have hl : raw23740step2Labels = labelEmbedding1 ∘ raw23740step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23740step2 raw23740step2Labels raw23740step3Labels labelEmbedding1 hl
    _ = mixedMoment B node800 node800Labels := by rfl

def raw23741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23741step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23741 raw23741Labels = mixedMoment B node749 node749Labels := by
  calc
    mixedMoment B raw23741 raw23741Labels = mixedMoment B raw23741step0 raw23741step0Labels := by
      have ha : raw23741step0 = (fun i j => raw23741 (permutation183 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23741step0 raw23741; decide +kernel
      have hl : raw23741step0Labels = raw23741Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23741 raw23741Labels permutation183 permutation7
    mixedMoment B raw23741step0 raw23741step0Labels = mixedMoment B raw23741step1 raw23741step1Labels := by
      have ha : raw23741step1 = -raw23741step0 := by apply Matrix.ext; change ∀ i j, raw23741step1 i j = -(raw23741step0 i j); unfold raw23741step1 raw23741step0; decide +kernel
      have hl : raw23741step1Labels = raw23741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23741step1 raw23741step1Labels = mixedMoment B raw23741step2 raw23741step2Labels := by
      have ha : raw23741step2 = raw23741step1 := by apply Matrix.ext; unfold raw23741step2 raw23741step1; decide +kernel
      have hl : raw23741step1Labels = labelEmbedding1 ∘ raw23741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23741step1 raw23741step1Labels raw23741step2Labels labelEmbedding1 hl
    _ = mixedMoment B node749 node749Labels := by rfl

def raw23742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23742 raw23742Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw23742 raw23742Labels = mixedMoment B raw23742step0 raw23742step0Labels := by
      have hz : ∀ j, raw23742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23742step0 = (fun i j => raw23742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23742step0 raw23742; decide +kernel
      have hl : raw23742step0Labels = raw23742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23742 raw23742Labels permutation346 hz
    mixedMoment B raw23742step0 raw23742step0Labels = mixedMoment B raw23742step1 raw23742step1Labels := by
      have ha : raw23742step1 = (fun i j => raw23742step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23742step1 raw23742step0; decide +kernel
      have hl : raw23742step1Labels = raw23742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23742step0 raw23742step0Labels permutation39 permutation7
    mixedMoment B raw23742step1 raw23742step1Labels = mixedMoment B raw23742step2 raw23742step2Labels := by
      have ha : raw23742step2 = -raw23742step1 := by apply Matrix.ext; change ∀ i j, raw23742step2 i j = -(raw23742step1 i j); unfold raw23742step2 raw23742step1; decide +kernel
      have hl : raw23742step2Labels = raw23742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23742step2 raw23742step2Labels = mixedMoment B raw23742step3 raw23742step3Labels := by
      have ha : raw23742step3 = raw23742step2 := by apply Matrix.ext; unfold raw23742step3 raw23742step2; decide +kernel
      have hl : raw23742step2Labels = labelEmbedding1 ∘ raw23742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23742step2 raw23742step2Labels raw23742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node807 node807Labels := by rfl

def raw23743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23743 raw23743Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw23743 raw23743Labels = mixedMoment B raw23743step0 raw23743step0Labels := by
      have hz : ∀ j, raw23743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23743step0 = (fun i j => raw23743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23743step0 raw23743; decide +kernel
      have hl : raw23743step0Labels = raw23743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23743 raw23743Labels permutation346 hz
    mixedMoment B raw23743step0 raw23743step0Labels = mixedMoment B raw23743step1 raw23743step1Labels := by
      have ha : raw23743step1 = (fun i j => raw23743step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23743step1 raw23743step0; decide +kernel
      have hl : raw23743step1Labels = raw23743step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23743step0 raw23743step0Labels permutation39 permutation7
    mixedMoment B raw23743step1 raw23743step1Labels = mixedMoment B raw23743step2 raw23743step2Labels := by
      have ha : raw23743step2 = -raw23743step1 := by apply Matrix.ext; change ∀ i j, raw23743step2 i j = -(raw23743step1 i j); unfold raw23743step2 raw23743step1; decide +kernel
      have hl : raw23743step2Labels = raw23743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23743step2 raw23743step2Labels = mixedMoment B raw23743step3 raw23743step3Labels := by
      have ha : raw23743step3 = raw23743step2 := by apply Matrix.ext; unfold raw23743step3 raw23743step2; decide +kernel
      have hl : raw23743step2Labels = labelEmbedding1 ∘ raw23743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23743step2 raw23743step2Labels raw23743step3Labels labelEmbedding1 hl
    _ = mixedMoment B node806 node806Labels := by rfl

def raw23744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23744step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw23744step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23744step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23744step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23744step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23744step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23744 raw23744Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw23744 raw23744Labels = mixedMoment B raw23744step0 raw23744step0Labels := by
      have hz : ∀ j, raw23744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23744step0 = (fun i j => raw23744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23744step0 raw23744; decide +kernel
      have hl : raw23744step0Labels = raw23744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23744 raw23744Labels permutation434 hz
    mixedMoment B raw23744step0 raw23744step0Labels = mixedMoment B raw23744step1 raw23744step1Labels := by
      have hz : ∀ j, raw23744step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23744step1 = (fun i j => raw23744step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23744step1 raw23744step0; decide +kernel
      have hl : raw23744step1Labels = raw23744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23744step0 raw23744step0Labels permutation80 hz
    mixedMoment B raw23744step1 raw23744step1Labels = mixedMoment B raw23744step2 raw23744step2Labels := by
      have ha : raw23744step2 = (fun i j => raw23744step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23744step2 raw23744step1; decide +kernel
      have hl : raw23744step2Labels = raw23744step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23744step1 raw23744step1Labels permutation9 permutation7
    mixedMoment B raw23744step2 raw23744step2Labels = mixedMoment B raw23744step3 raw23744step3Labels := by
      have ha : raw23744step3 = -raw23744step2 := by apply Matrix.ext; change ∀ i j, raw23744step3 i j = -(raw23744step2 i j); unfold raw23744step3 raw23744step2; decide +kernel
      have hl : raw23744step3Labels = raw23744step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23744step3 raw23744step3Labels = mixedMoment B raw23744step4 raw23744step4Labels := by
      have ha : raw23744step4 = raw23744step3 := by apply Matrix.ext; unfold raw23744step4 raw23744step3; decide +kernel
      have hl : raw23744step3Labels = labelEmbedding1 ∘ raw23744step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23744step3 raw23744step3Labels raw23744step4Labels labelEmbedding1 hl
    _ = mixedMoment B node684 node684Labels := by rfl

def raw23745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23745step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23745step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23745step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23745step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23745step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23745 raw23745Labels = mixedMoment B node843 node843Labels := by
  calc
    mixedMoment B raw23745 raw23745Labels = mixedMoment B raw23745step0 raw23745step0Labels := by
      have hz : ∀ j, raw23745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23745step0 = (fun i j => raw23745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23745step0 raw23745; decide +kernel
      have hl : raw23745step0Labels = raw23745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23745 raw23745Labels permutation434 hz
    mixedMoment B raw23745step0 raw23745step0Labels = mixedMoment B raw23745step1 raw23745step1Labels := by
      have hz : ∀ j, raw23745step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23745step1 = (fun i j => raw23745step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23745step1 raw23745step0; decide +kernel
      have hl : raw23745step1Labels = raw23745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23745step0 raw23745step0Labels permutation80 hz
    mixedMoment B raw23745step1 raw23745step1Labels = mixedMoment B raw23745step2 raw23745step2Labels := by
      have ha : raw23745step2 = (fun i j => raw23745step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23745step2 raw23745step1; decide +kernel
      have hl : raw23745step2Labels = raw23745step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23745step1 raw23745step1Labels permutation9 permutation7
    mixedMoment B raw23745step2 raw23745step2Labels = mixedMoment B raw23745step3 raw23745step3Labels := by
      have ha : raw23745step3 = -raw23745step2 := by apply Matrix.ext; change ∀ i j, raw23745step3 i j = -(raw23745step2 i j); unfold raw23745step3 raw23745step2; decide +kernel
      have hl : raw23745step3Labels = raw23745step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23745step3 raw23745step3Labels = mixedMoment B raw23745step4 raw23745step4Labels := by
      have ha : raw23745step4 = raw23745step3 := by apply Matrix.ext; unfold raw23745step4 raw23745step3; decide +kernel
      have hl : raw23745step3Labels = labelEmbedding1 ∘ raw23745step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23745step3 raw23745step3Labels raw23745step4Labels labelEmbedding1 hl
    _ = mixedMoment B node843 node843Labels := by rfl

def raw23746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw23746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23746step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23746step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23746 raw23746Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw23746 raw23746Labels = mixedMoment B raw23746step0 raw23746step0Labels := by
      have hz : ∀ j, raw23746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23746step0 = (fun i j => raw23746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23746step0 raw23746; decide +kernel
      have hl : raw23746step0Labels = raw23746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23746 raw23746Labels permutation434 hz
    mixedMoment B raw23746step0 raw23746step0Labels = mixedMoment B raw23746step1 raw23746step1Labels := by
      have ha : raw23746step1 = (fun i j => raw23746step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23746step1 raw23746step0; decide +kernel
      have hl : raw23746step1Labels = raw23746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23746step0 raw23746step0Labels permutation39 permutation7
    mixedMoment B raw23746step1 raw23746step1Labels = mixedMoment B raw23746step2 raw23746step2Labels := by
      have ha : raw23746step2 = -raw23746step1 := by apply Matrix.ext; change ∀ i j, raw23746step2 i j = -(raw23746step1 i j); unfold raw23746step2 raw23746step1; decide +kernel
      have hl : raw23746step2Labels = raw23746step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23746step2 raw23746step2Labels = mixedMoment B raw23746step3 raw23746step3Labels := by
      have ha : raw23746step3 = raw23746step2 := by apply Matrix.ext; unfold raw23746step3 raw23746step2; decide +kernel
      have hl : raw23746step2Labels = labelEmbedding1 ∘ raw23746step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23746step2 raw23746step2Labels raw23746step3Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

def raw23747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw23747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw23747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23747 raw23747Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw23747 raw23747Labels = mixedMoment B raw23747step0 raw23747step0Labels := by
      have hz : ∀ j, raw23747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23747step0 = (fun i j => raw23747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23747step0 raw23747; decide +kernel
      have hl : raw23747step0Labels = raw23747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23747 raw23747Labels permutation346 hz
    mixedMoment B raw23747step0 raw23747step0Labels = mixedMoment B raw23747step1 raw23747step1Labels := by
      have ha : raw23747step1 = (fun i j => raw23747step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23747step1 raw23747step0; decide +kernel
      have hl : raw23747step1Labels = raw23747step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23747step0 raw23747step0Labels permutation39 permutation7
    mixedMoment B raw23747step1 raw23747step1Labels = mixedMoment B raw23747step2 raw23747step2Labels := by
      have ha : raw23747step2 = -raw23747step1 := by apply Matrix.ext; change ∀ i j, raw23747step2 i j = -(raw23747step1 i j); unfold raw23747step2 raw23747step1; decide +kernel
      have hl : raw23747step2Labels = raw23747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23747step2 raw23747step2Labels = mixedMoment B raw23747step3 raw23747step3Labels := by
      have ha : raw23747step3 = raw23747step2 := by apply Matrix.ext; unfold raw23747step3 raw23747step2; decide +kernel
      have hl : raw23747step2Labels = labelEmbedding1 ∘ raw23747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23747step2 raw23747step2Labels raw23747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

def raw23748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![3, -1, -2], ![1, 0, -1]]
def raw23748step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw23748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw23748step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23748step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw23748step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23748 raw23748Labels = mixedMoment B node851 node851Labels := by
  calc
    mixedMoment B raw23748 raw23748Labels = mixedMoment B raw23748step0 raw23748step0Labels := by
      have hz : ∀ j, raw23748 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23748step0 = (fun i j => raw23748 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23748step0 raw23748; decide +kernel
      have hl : raw23748step0Labels = raw23748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23748 raw23748Labels permutation434 hz
    mixedMoment B raw23748step0 raw23748step0Labels = mixedMoment B raw23748step1 raw23748step1Labels := by
      have hz : ∀ j, raw23748step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23748step1 = (fun i j => raw23748step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23748step1 raw23748step0; decide +kernel
      have hl : raw23748step1Labels = raw23748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23748step0 raw23748step0Labels permutation80 hz
    mixedMoment B raw23748step1 raw23748step1Labels = mixedMoment B raw23748step2 raw23748step2Labels := by
      have ha : raw23748step2 = (fun i j => raw23748step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23748step2 raw23748step1; decide +kernel
      have hl : raw23748step2Labels = raw23748step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23748step1 raw23748step1Labels permutation9 permutation7
    mixedMoment B raw23748step2 raw23748step2Labels = mixedMoment B raw23748step3 raw23748step3Labels := by
      have ha : raw23748step3 = -raw23748step2 := by apply Matrix.ext; change ∀ i j, raw23748step3 i j = -(raw23748step2 i j); unfold raw23748step3 raw23748step2; decide +kernel
      have hl : raw23748step3Labels = raw23748step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23748step3 raw23748step3Labels = mixedMoment B raw23748step4 raw23748step4Labels := by
      have ha : raw23748step4 = raw23748step3 := by apply Matrix.ext; unfold raw23748step4 raw23748step3; decide +kernel
      have hl : raw23748step3Labels = labelEmbedding1 ∘ raw23748step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23748step3 raw23748step3Labels raw23748step4Labels labelEmbedding1 hl
    _ = mixedMoment B node851 node851Labels := by rfl

def raw23749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23749step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw23749step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23749step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23749step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23749step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23749 raw23749Labels = mixedMoment B node685 node685Labels := by
  calc
    mixedMoment B raw23749 raw23749Labels = mixedMoment B raw23749step0 raw23749step0Labels := by
      have hz : ∀ j, raw23749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23749step0 = (fun i j => raw23749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23749step0 raw23749; decide +kernel
      have hl : raw23749step0Labels = raw23749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23749 raw23749Labels permutation434 hz
    mixedMoment B raw23749step0 raw23749step0Labels = mixedMoment B raw23749step1 raw23749step1Labels := by
      have hz : ∀ j, raw23749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23749step1 = (fun i j => raw23749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23749step1 raw23749step0; decide +kernel
      have hl : raw23749step1Labels = raw23749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23749step0 raw23749step0Labels permutation80 hz
    mixedMoment B raw23749step1 raw23749step1Labels = mixedMoment B raw23749step2 raw23749step2Labels := by
      have ha : raw23749step2 = (fun i j => raw23749step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23749step2 raw23749step1; decide +kernel
      have hl : raw23749step2Labels = raw23749step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23749step1 raw23749step1Labels permutation9 permutation7
    mixedMoment B raw23749step2 raw23749step2Labels = mixedMoment B raw23749step3 raw23749step3Labels := by
      have ha : raw23749step3 = -raw23749step2 := by apply Matrix.ext; change ∀ i j, raw23749step3 i j = -(raw23749step2 i j); unfold raw23749step3 raw23749step2; decide +kernel
      have hl : raw23749step3Labels = raw23749step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23749step3 raw23749step3Labels = mixedMoment B raw23749step4 raw23749step4Labels := by
      have ha : raw23749step4 = raw23749step3 := by apply Matrix.ext; unfold raw23749step4 raw23749step3; decide +kernel
      have hl : raw23749step3Labels = labelEmbedding1 ∘ raw23749step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23749step3 raw23749step3Labels raw23749step4Labels labelEmbedding1 hl
    _ = mixedMoment B node685 node685Labels := by rfl

def raw23750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23750step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw23750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23750step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw23750step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23750step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw23750step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23750 raw23750Labels = mixedMoment B node844 node844Labels := by
  calc
    mixedMoment B raw23750 raw23750Labels = mixedMoment B raw23750step0 raw23750step0Labels := by
      have hz : ∀ j, raw23750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23750step0 = (fun i j => raw23750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23750step0 raw23750; decide +kernel
      have hl : raw23750step0Labels = raw23750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23750 raw23750Labels permutation434 hz
    mixedMoment B raw23750step0 raw23750step0Labels = mixedMoment B raw23750step1 raw23750step1Labels := by
      have hz : ∀ j, raw23750step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23750step1 = (fun i j => raw23750step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23750step1 raw23750step0; decide +kernel
      have hl : raw23750step1Labels = raw23750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23750step0 raw23750step0Labels permutation80 hz
    mixedMoment B raw23750step1 raw23750step1Labels = mixedMoment B raw23750step2 raw23750step2Labels := by
      have ha : raw23750step2 = (fun i j => raw23750step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23750step2 raw23750step1; decide +kernel
      have hl : raw23750step2Labels = raw23750step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23750step1 raw23750step1Labels permutation9 permutation7
    mixedMoment B raw23750step2 raw23750step2Labels = mixedMoment B raw23750step3 raw23750step3Labels := by
      have ha : raw23750step3 = -raw23750step2 := by apply Matrix.ext; change ∀ i j, raw23750step3 i j = -(raw23750step2 i j); unfold raw23750step3 raw23750step2; decide +kernel
      have hl : raw23750step3Labels = raw23750step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23750step3 raw23750step3Labels = mixedMoment B raw23750step4 raw23750step4Labels := by
      have ha : raw23750step4 = raw23750step3 := by apply Matrix.ext; unfold raw23750step4 raw23750step3; decide +kernel
      have hl : raw23750step3Labels = labelEmbedding1 ∘ raw23750step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23750step3 raw23750step3Labels raw23750step4Labels labelEmbedding1 hl
    _ = mixedMoment B node844 node844Labels := by rfl

def raw23751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw23751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23751step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23751step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23751step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23751 raw23751Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw23751 raw23751Labels = mixedMoment B raw23751step0 raw23751step0Labels := by
      have hz : ∀ j, raw23751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23751step0 = (fun i j => raw23751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23751step0 raw23751; decide +kernel
      have hl : raw23751step0Labels = raw23751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23751 raw23751Labels permutation434 hz
    mixedMoment B raw23751step0 raw23751step0Labels = mixedMoment B raw23751step1 raw23751step1Labels := by
      have ha : raw23751step1 = (fun i j => raw23751step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23751step1 raw23751step0; decide +kernel
      have hl : raw23751step1Labels = raw23751step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23751step0 raw23751step0Labels permutation39 permutation7
    mixedMoment B raw23751step1 raw23751step1Labels = mixedMoment B raw23751step2 raw23751step2Labels := by
      have ha : raw23751step2 = -raw23751step1 := by apply Matrix.ext; change ∀ i j, raw23751step2 i j = -(raw23751step1 i j); unfold raw23751step2 raw23751step1; decide +kernel
      have hl : raw23751step2Labels = raw23751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23751step2 raw23751step2Labels = mixedMoment B raw23751step3 raw23751step3Labels := by
      have ha : raw23751step3 = raw23751step2 := by apply Matrix.ext; unfold raw23751step3 raw23751step2; decide +kernel
      have hl : raw23751step2Labels = labelEmbedding1 ∘ raw23751step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23751step2 raw23751step2Labels raw23751step3Labels labelEmbedding1 hl
    _ = mixedMoment B node764 node764Labels := by rfl

def raw23752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw23752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw23752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23752 raw23752Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw23752 raw23752Labels = mixedMoment B raw23752step0 raw23752step0Labels := by
      have hz : ∀ j, raw23752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23752step0 = (fun i j => raw23752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23752step0 raw23752; decide +kernel
      have hl : raw23752step0Labels = raw23752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23752 raw23752Labels permutation346 hz
    mixedMoment B raw23752step0 raw23752step0Labels = mixedMoment B raw23752step1 raw23752step1Labels := by
      have ha : raw23752step1 = (fun i j => raw23752step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23752step1 raw23752step0; decide +kernel
      have hl : raw23752step1Labels = raw23752step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23752step0 raw23752step0Labels permutation39 permutation7
    mixedMoment B raw23752step1 raw23752step1Labels = mixedMoment B raw23752step2 raw23752step2Labels := by
      have ha : raw23752step2 = -raw23752step1 := by apply Matrix.ext; change ∀ i j, raw23752step2 i j = -(raw23752step1 i j); unfold raw23752step2 raw23752step1; decide +kernel
      have hl : raw23752step2Labels = raw23752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23752step2 raw23752step2Labels = mixedMoment B raw23752step3 raw23752step3Labels := by
      have ha : raw23752step3 = raw23752step2 := by apply Matrix.ext; unfold raw23752step3 raw23752step2; decide +kernel
      have hl : raw23752step2Labels = labelEmbedding1 ∘ raw23752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23752step2 raw23752step2Labels raw23752step3Labels labelEmbedding1 hl
    _ = mixedMoment B node764 node764Labels := by rfl

def raw23753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw23753step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw23753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw23753step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23753step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw23753step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23753 raw23753Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw23753 raw23753Labels = mixedMoment B raw23753step0 raw23753step0Labels := by
      have hz : ∀ j, raw23753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23753step0 = (fun i j => raw23753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23753step0 raw23753; decide +kernel
      have hl : raw23753step0Labels = raw23753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23753 raw23753Labels permutation434 hz
    mixedMoment B raw23753step0 raw23753step0Labels = mixedMoment B raw23753step1 raw23753step1Labels := by
      have hz : ∀ j, raw23753step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23753step1 = (fun i j => raw23753step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23753step1 raw23753step0; decide +kernel
      have hl : raw23753step1Labels = raw23753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23753step0 raw23753step0Labels permutation80 hz
    mixedMoment B raw23753step1 raw23753step1Labels = mixedMoment B raw23753step2 raw23753step2Labels := by
      have ha : raw23753step2 = (fun i j => raw23753step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23753step2 raw23753step1; decide +kernel
      have hl : raw23753step2Labels = raw23753step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23753step1 raw23753step1Labels permutation9 permutation7
    mixedMoment B raw23753step2 raw23753step2Labels = mixedMoment B raw23753step3 raw23753step3Labels := by
      have ha : raw23753step3 = -raw23753step2 := by apply Matrix.ext; change ∀ i j, raw23753step3 i j = -(raw23753step2 i j); unfold raw23753step3 raw23753step2; decide +kernel
      have hl : raw23753step3Labels = raw23753step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23753step3 raw23753step3Labels = mixedMoment B raw23753step4 raw23753step4Labels := by
      have ha : raw23753step4 = raw23753step3 := by apply Matrix.ext; unfold raw23753step4 raw23753step3; decide +kernel
      have hl : raw23753step3Labels = labelEmbedding1 ∘ raw23753step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23753step3 raw23753step3Labels raw23753step4Labels labelEmbedding1 hl
    _ = mixedMoment B node853 node853Labels := by rfl

def raw23754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23754 raw23754Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw23754 raw23754Labels = mixedMoment B raw23754step0 raw23754step0Labels := by
      have hz : ∀ j, raw23754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23754step0 = (fun i j => raw23754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23754step0 raw23754; decide +kernel
      have hl : raw23754step0Labels = raw23754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23754 raw23754Labels permutation434 hz
    mixedMoment B raw23754step0 raw23754step0Labels = mixedMoment B raw23754step1 raw23754step1Labels := by
      have hz : ∀ j, raw23754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23754step1 = (fun i j => raw23754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23754step1 raw23754step0; decide +kernel
      have hl : raw23754step1Labels = raw23754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23754step0 raw23754step0Labels permutation80 hz
    mixedMoment B raw23754step1 raw23754step1Labels = mixedMoment B raw23754step2 raw23754step2Labels := by
      have ha : raw23754step2 = (fun i j => raw23754step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23754step2 raw23754step1; decide +kernel
      have hl : raw23754step2Labels = raw23754step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23754step1 raw23754step1Labels permutation9 permutation2
    _ = mixedMoment B node1653 node1653Labels := by rfl

def raw23755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23755 raw23755Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw23755 raw23755Labels = mixedMoment B raw23755step0 raw23755step0Labels := by
      have hz : ∀ j, raw23755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23755step0 = (fun i j => raw23755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23755step0 raw23755; decide +kernel
      have hl : raw23755step0Labels = raw23755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23755 raw23755Labels permutation434 hz
    mixedMoment B raw23755step0 raw23755step0Labels = mixedMoment B raw23755step1 raw23755step1Labels := by
      have ha : raw23755step1 = (fun i j => raw23755step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23755step1 raw23755step0; decide +kernel
      have hl : raw23755step1Labels = raw23755step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23755step0 raw23755step0Labels permutation39 permutation2
    _ = mixedMoment B node1605 node1605Labels := by rfl

def raw23756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23756 raw23756Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw23756 raw23756Labels = mixedMoment B raw23756step0 raw23756step0Labels := by
      have hz : ∀ j, raw23756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23756step0 = (fun i j => raw23756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23756step0 raw23756; decide +kernel
      have hl : raw23756step0Labels = raw23756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23756 raw23756Labels permutation346 hz
    mixedMoment B raw23756step0 raw23756step0Labels = mixedMoment B raw23756step1 raw23756step1Labels := by
      have ha : raw23756step1 = (fun i j => raw23756step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23756step1 raw23756step0; decide +kernel
      have hl : raw23756step1Labels = raw23756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23756step0 raw23756step0Labels permutation39 permutation2
    _ = mixedMoment B node1605 node1605Labels := by rfl

def raw23757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw23757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23757 raw23757Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw23757 raw23757Labels = mixedMoment B raw23757step0 raw23757step0Labels := by
      have hz : ∀ j, raw23757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23757step0 = (fun i j => raw23757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23757step0 raw23757; decide +kernel
      have hl : raw23757step0Labels = raw23757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23757 raw23757Labels permutation434 hz
    mixedMoment B raw23757step0 raw23757step0Labels = mixedMoment B raw23757step1 raw23757step1Labels := by
      have hz : ∀ j, raw23757step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23757step1 = (fun i j => raw23757step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23757step1 raw23757step0; decide +kernel
      have hl : raw23757step1Labels = raw23757step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23757step0 raw23757step0Labels permutation80 hz
    mixedMoment B raw23757step1 raw23757step1Labels = mixedMoment B raw23757step2 raw23757step2Labels := by
      have ha : raw23757step2 = (fun i j => raw23757step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23757step2 raw23757step1; decide +kernel
      have hl : raw23757step2Labels = raw23757step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23757step1 raw23757step1Labels permutation9 permutation2
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw23758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw23758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23758 raw23758Labels = mixedMoment B node561 node561Labels := by
  calc
    mixedMoment B raw23758 raw23758Labels = mixedMoment B raw23758step0 raw23758step0Labels := by
      have hz : ∀ j, raw23758 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23758step0 = (fun i j => raw23758 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23758step0 raw23758; decide +kernel
      have hl : raw23758step0Labels = raw23758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23758 raw23758Labels permutation434 hz
    mixedMoment B raw23758step0 raw23758step0Labels = mixedMoment B raw23758step1 raw23758step1Labels := by
      have hz : ∀ j, raw23758step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23758step1 = (fun i j => raw23758step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23758step1 raw23758step0; decide +kernel
      have hl : raw23758step1Labels = raw23758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23758step0 raw23758step0Labels permutation80 hz
    mixedMoment B raw23758step1 raw23758step1Labels = mixedMoment B raw23758step2 raw23758step2Labels := by
      have ha : raw23758step2 = (fun i j => raw23758step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23758step2 raw23758step1; decide +kernel
      have hl : raw23758step2Labels = raw23758step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23758step1 raw23758step1Labels permutation9 permutation2
    _ = mixedMoment B node561 node561Labels := by rfl

def raw23759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23759 raw23759Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw23759 raw23759Labels = mixedMoment B raw23759step0 raw23759step0Labels := by
      have hz : ∀ j, raw23759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23759step0 = (fun i j => raw23759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23759step0 raw23759; decide +kernel
      have hl : raw23759step0Labels = raw23759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23759 raw23759Labels permutation434 hz
    mixedMoment B raw23759step0 raw23759step0Labels = mixedMoment B raw23759step1 raw23759step1Labels := by
      have ha : raw23759step1 = (fun i j => raw23759step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23759step1 raw23759step0; decide +kernel
      have hl : raw23759step1Labels = raw23759step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23759step0 raw23759step0Labels permutation33 permutation2
    _ = mixedMoment B node539 node539Labels := by rfl

def raw23760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23760 raw23760Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw23760 raw23760Labels = mixedMoment B raw23760step0 raw23760step0Labels := by
      have hz : ∀ j, raw23760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23760step0 = (fun i j => raw23760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23760step0 raw23760; decide +kernel
      have hl : raw23760step0Labels = raw23760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23760 raw23760Labels permutation346 hz
    mixedMoment B raw23760step0 raw23760step0Labels = mixedMoment B raw23760step1 raw23760step1Labels := by
      have ha : raw23760step1 = (fun i j => raw23760step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23760step1 raw23760step0; decide +kernel
      have hl : raw23760step1Labels = raw23760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23760step0 raw23760step0Labels permutation33 permutation2
    _ = mixedMoment B node539 node539Labels := by rfl

def raw23761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23761 raw23761Labels = mixedMoment B node547 node547Labels := by
  calc
    mixedMoment B raw23761 raw23761Labels = mixedMoment B raw23761step0 raw23761step0Labels := by
      have hz : ∀ j, raw23761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23761step0 = (fun i j => raw23761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23761step0 raw23761; decide +kernel
      have hl : raw23761step0Labels = raw23761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23761 raw23761Labels permutation434 hz
    mixedMoment B raw23761step0 raw23761step0Labels = mixedMoment B raw23761step1 raw23761step1Labels := by
      have hz : ∀ j, raw23761step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23761step1 = (fun i j => raw23761step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23761step1 raw23761step0; decide +kernel
      have hl : raw23761step1Labels = raw23761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23761step0 raw23761step0Labels permutation80 hz
    mixedMoment B raw23761step1 raw23761step1Labels = mixedMoment B raw23761step2 raw23761step2Labels := by
      have ha : raw23761step2 = (fun i j => raw23761step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23761step2 raw23761step1; decide +kernel
      have hl : raw23761step2Labels = raw23761step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23761step1 raw23761step1Labels permutation9 permutation2
    _ = mixedMoment B node547 node547Labels := by rfl

def raw23762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23762 raw23762Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw23762 raw23762Labels = mixedMoment B raw23762step0 raw23762step0Labels := by
      have hz : ∀ j, raw23762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23762step0 = (fun i j => raw23762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23762step0 raw23762; decide +kernel
      have hl : raw23762step0Labels = raw23762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23762 raw23762Labels permutation434 hz
    mixedMoment B raw23762step0 raw23762step0Labels = mixedMoment B raw23762step1 raw23762step1Labels := by
      have ha : raw23762step1 = (fun i j => raw23762step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23762step1 raw23762step0; decide +kernel
      have hl : raw23762step1Labels = raw23762step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23762step0 raw23762step0Labels permutation33 permutation2
    _ = mixedMoment B node734 node734Labels := by rfl

def raw23763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23763 raw23763Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw23763 raw23763Labels = mixedMoment B raw23763step0 raw23763step0Labels := by
      have hz : ∀ j, raw23763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23763step0 = (fun i j => raw23763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23763step0 raw23763; decide +kernel
      have hl : raw23763step0Labels = raw23763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23763 raw23763Labels permutation346 hz
    mixedMoment B raw23763step0 raw23763step0Labels = mixedMoment B raw23763step1 raw23763step1Labels := by
      have ha : raw23763step1 = (fun i j => raw23763step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23763step1 raw23763step0; decide +kernel
      have hl : raw23763step1Labels = raw23763step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23763step0 raw23763step0Labels permutation33 permutation2
    _ = mixedMoment B node734 node734Labels := by rfl

def raw23764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw23764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23764 raw23764Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw23764 raw23764Labels = mixedMoment B raw23764step0 raw23764step0Labels := by
      have hz : ∀ j, raw23764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23764step0 = (fun i j => raw23764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23764step0 raw23764; decide +kernel
      have hl : raw23764step0Labels = raw23764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23764 raw23764Labels permutation434 hz
    mixedMoment B raw23764step0 raw23764step0Labels = mixedMoment B raw23764step1 raw23764step1Labels := by
      have hz : ∀ j, raw23764step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23764step1 = (fun i j => raw23764step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23764step1 raw23764step0; decide +kernel
      have hl : raw23764step1Labels = raw23764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23764step0 raw23764step0Labels permutation80 hz
    mixedMoment B raw23764step1 raw23764step1Labels = mixedMoment B raw23764step2 raw23764step2Labels := by
      have ha : raw23764step2 = (fun i j => raw23764step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23764step2 raw23764step1; decide +kernel
      have hl : raw23764step2Labels = raw23764step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23764step1 raw23764step1Labels permutation9 permutation2
    _ = mixedMoment B node742 node742Labels := by rfl

def raw23765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23765step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23765step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23765step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23765step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23765 raw23765Labels = mixedMoment B node4132 node4132Labels := by
  calc
    mixedMoment B raw23765 raw23765Labels = mixedMoment B raw23765step0 raw23765step0Labels := by
      have hz : ∀ j, raw23765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23765step0 = (fun i j => raw23765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23765step0 raw23765; decide +kernel
      have hl : raw23765step0Labels = raw23765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23765 raw23765Labels permutation434 hz
    mixedMoment B raw23765step0 raw23765step0Labels = mixedMoment B raw23765step1 raw23765step1Labels := by
      have hz : ∀ j, raw23765step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23765step1 = (fun i j => raw23765step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23765step1 raw23765step0; decide +kernel
      have hl : raw23765step1Labels = raw23765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23765step0 raw23765step0Labels permutation80 hz
    mixedMoment B raw23765step1 raw23765step1Labels = mixedMoment B raw23765step2 raw23765step2Labels := by
      have ha : raw23765step2 = (fun i j => raw23765step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23765step2 raw23765step1; decide +kernel
      have hl : raw23765step2Labels = raw23765step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23765step1 raw23765step1Labels permutation12 permutation4
    mixedMoment B raw23765step2 raw23765step2Labels = mixedMoment B raw23765step3 raw23765step3Labels := by
      have ha : raw23765step3 = -raw23765step2 := by apply Matrix.ext; change ∀ i j, raw23765step3 i j = -(raw23765step2 i j); unfold raw23765step3 raw23765step2; decide +kernel
      have hl : raw23765step3Labels = raw23765step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23765step3 raw23765step3Labels = mixedMoment B raw23765step4 raw23765step4Labels := by
      have ha : raw23765step4 = raw23765step3 := by apply Matrix.ext; unfold raw23765step4 raw23765step3; decide +kernel
      have hl : raw23765step3Labels = labelEmbedding7 ∘ raw23765step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23765step3 raw23765step3Labels raw23765step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4132 node4132Labels := by rfl

def raw23766 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23766step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23766step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23766 raw23766Labels = mixedMoment B node4223 node4223Labels := by
  calc
    mixedMoment B raw23766 raw23766Labels = mixedMoment B raw23766step0 raw23766step0Labels := by
      have hz : ∀ j, raw23766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23766step0 = (fun i j => raw23766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23766step0 raw23766; decide +kernel
      have hl : raw23766step0Labels = raw23766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23766 raw23766Labels permutation434 hz
    mixedMoment B raw23766step0 raw23766step0Labels = mixedMoment B raw23766step1 raw23766step1Labels := by
      have ha : raw23766step1 = (fun i j => raw23766step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23766step1 raw23766step0; decide +kernel
      have hl : raw23766step1Labels = raw23766step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23766step0 raw23766step0Labels permutation42 permutation4
    mixedMoment B raw23766step1 raw23766step1Labels = mixedMoment B raw23766step2 raw23766step2Labels := by
      have ha : raw23766step2 = -raw23766step1 := by apply Matrix.ext; change ∀ i j, raw23766step2 i j = -(raw23766step1 i j); unfold raw23766step2 raw23766step1; decide +kernel
      have hl : raw23766step2Labels = raw23766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23766step2 raw23766step2Labels = mixedMoment B raw23766step3 raw23766step3Labels := by
      have ha : raw23766step3 = raw23766step2 := by apply Matrix.ext; unfold raw23766step3 raw23766step2; decide +kernel
      have hl : raw23766step2Labels = labelEmbedding7 ∘ raw23766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23766step2 raw23766step2Labels raw23766step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4223 node4223Labels := by rfl

def raw23767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23767step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23767step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23767 raw23767Labels = mixedMoment B node4223 node4223Labels := by
  calc
    mixedMoment B raw23767 raw23767Labels = mixedMoment B raw23767step0 raw23767step0Labels := by
      have hz : ∀ j, raw23767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23767step0 = (fun i j => raw23767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23767step0 raw23767; decide +kernel
      have hl : raw23767step0Labels = raw23767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23767 raw23767Labels permutation346 hz
    mixedMoment B raw23767step0 raw23767step0Labels = mixedMoment B raw23767step1 raw23767step1Labels := by
      have ha : raw23767step1 = (fun i j => raw23767step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23767step1 raw23767step0; decide +kernel
      have hl : raw23767step1Labels = raw23767step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23767step0 raw23767step0Labels permutation42 permutation4
    mixedMoment B raw23767step1 raw23767step1Labels = mixedMoment B raw23767step2 raw23767step2Labels := by
      have ha : raw23767step2 = -raw23767step1 := by apply Matrix.ext; change ∀ i j, raw23767step2 i j = -(raw23767step1 i j); unfold raw23767step2 raw23767step1; decide +kernel
      have hl : raw23767step2Labels = raw23767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23767step2 raw23767step2Labels = mixedMoment B raw23767step3 raw23767step3Labels := by
      have ha : raw23767step3 = raw23767step2 := by apply Matrix.ext; unfold raw23767step3 raw23767step2; decide +kernel
      have hl : raw23767step2Labels = labelEmbedding7 ∘ raw23767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23767step2 raw23767step2Labels raw23767step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4223 node4223Labels := by rfl

def raw23768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23768step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23768step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23768step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23768 raw23768Labels = mixedMoment B node4115 node4115Labels := by
  calc
    mixedMoment B raw23768 raw23768Labels = mixedMoment B raw23768step0 raw23768step0Labels := by
      have hz : ∀ j, raw23768 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23768step0 = (fun i j => raw23768 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23768step0 raw23768; decide +kernel
      have hl : raw23768step0Labels = raw23768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23768 raw23768Labels permutation434 hz
    mixedMoment B raw23768step0 raw23768step0Labels = mixedMoment B raw23768step1 raw23768step1Labels := by
      have ha : raw23768step1 = (fun i j => raw23768step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23768step1 raw23768step0; decide +kernel
      have hl : raw23768step1Labels = raw23768step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23768step0 raw23768step0Labels permutation33 permutation4
    mixedMoment B raw23768step1 raw23768step1Labels = mixedMoment B raw23768step2 raw23768step2Labels := by
      have ha : raw23768step2 = -raw23768step1 := by apply Matrix.ext; change ∀ i j, raw23768step2 i j = -(raw23768step1 i j); unfold raw23768step2 raw23768step1; decide +kernel
      have hl : raw23768step2Labels = raw23768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23768step2 raw23768step2Labels = mixedMoment B raw23768step3 raw23768step3Labels := by
      have ha : raw23768step3 = raw23768step2 := by apply Matrix.ext; unfold raw23768step3 raw23768step2; decide +kernel
      have hl : raw23768step2Labels = labelEmbedding7 ∘ raw23768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23768step2 raw23768step2Labels raw23768step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4115 node4115Labels := by rfl

def raw23769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23769step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23769step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23769 raw23769Labels = mixedMoment B node4207 node4207Labels := by
  calc
    mixedMoment B raw23769 raw23769Labels = mixedMoment B raw23769step0 raw23769step0Labels := by
      have ha : raw23769step0 = (fun i j => raw23769 (permutation201 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23769step0 raw23769; decide +kernel
      have hl : raw23769step0Labels = raw23769Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23769 raw23769Labels permutation201 permutation4
    mixedMoment B raw23769step0 raw23769step0Labels = mixedMoment B raw23769step1 raw23769step1Labels := by
      have ha : raw23769step1 = -raw23769step0 := by apply Matrix.ext; change ∀ i j, raw23769step1 i j = -(raw23769step0 i j); unfold raw23769step1 raw23769step0; decide +kernel
      have hl : raw23769step1Labels = raw23769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23769step1 raw23769step1Labels = mixedMoment B raw23769step2 raw23769step2Labels := by
      have ha : raw23769step2 = raw23769step1 := by apply Matrix.ext; unfold raw23769step2 raw23769step1; decide +kernel
      have hl : raw23769step1Labels = labelEmbedding7 ∘ raw23769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23769step1 raw23769step1Labels raw23769step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4207 node4207Labels := by rfl

def raw23770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23770step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23770step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23770step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23770step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23770 raw23770Labels = mixedMoment B node4115 node4115Labels := by
  calc
    mixedMoment B raw23770 raw23770Labels = mixedMoment B raw23770step0 raw23770step0Labels := by
      have hz : ∀ j, raw23770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23770step0 = (fun i j => raw23770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23770step0 raw23770; decide +kernel
      have hl : raw23770step0Labels = raw23770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23770 raw23770Labels permutation346 hz
    mixedMoment B raw23770step0 raw23770step0Labels = mixedMoment B raw23770step1 raw23770step1Labels := by
      have ha : raw23770step1 = (fun i j => raw23770step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23770step1 raw23770step0; decide +kernel
      have hl : raw23770step1Labels = raw23770step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23770step0 raw23770step0Labels permutation33 permutation4
    mixedMoment B raw23770step1 raw23770step1Labels = mixedMoment B raw23770step2 raw23770step2Labels := by
      have ha : raw23770step2 = -raw23770step1 := by apply Matrix.ext; change ∀ i j, raw23770step2 i j = -(raw23770step1 i j); unfold raw23770step2 raw23770step1; decide +kernel
      have hl : raw23770step2Labels = raw23770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23770step2 raw23770step2Labels = mixedMoment B raw23770step3 raw23770step3Labels := by
      have ha : raw23770step3 = raw23770step2 := by apply Matrix.ext; unfold raw23770step3 raw23770step2; decide +kernel
      have hl : raw23770step2Labels = labelEmbedding7 ∘ raw23770step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23770step2 raw23770step2Labels raw23770step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4115 node4115Labels := by rfl

def raw23771 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23771step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23771step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23771step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23771 raw23771Labels = mixedMoment B node4207 node4207Labels := by
  calc
    mixedMoment B raw23771 raw23771Labels = mixedMoment B raw23771step0 raw23771step0Labels := by
      have ha : raw23771step0 = (fun i j => raw23771 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23771step0 raw23771; decide +kernel
      have hl : raw23771step0Labels = raw23771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23771 raw23771Labels permutation177 permutation4
    mixedMoment B raw23771step0 raw23771step0Labels = mixedMoment B raw23771step1 raw23771step1Labels := by
      have ha : raw23771step1 = -raw23771step0 := by apply Matrix.ext; change ∀ i j, raw23771step1 i j = -(raw23771step0 i j); unfold raw23771step1 raw23771step0; decide +kernel
      have hl : raw23771step1Labels = raw23771step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23771step1 raw23771step1Labels = mixedMoment B raw23771step2 raw23771step2Labels := by
      have ha : raw23771step2 = raw23771step1 := by apply Matrix.ext; unfold raw23771step2 raw23771step1; decide +kernel
      have hl : raw23771step1Labels = labelEmbedding7 ∘ raw23771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23771step1 raw23771step1Labels raw23771step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4207 node4207Labels := by rfl

def raw23772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23772step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23772step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23772step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23772step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23772step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23772step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23772 raw23772Labels = mixedMoment B node4121 node4121Labels := by
  calc
    mixedMoment B raw23772 raw23772Labels = mixedMoment B raw23772step0 raw23772step0Labels := by
      have hz : ∀ j, raw23772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23772step0 = (fun i j => raw23772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23772step0 raw23772; decide +kernel
      have hl : raw23772step0Labels = raw23772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23772 raw23772Labels permutation434 hz
    mixedMoment B raw23772step0 raw23772step0Labels = mixedMoment B raw23772step1 raw23772step1Labels := by
      have hz : ∀ j, raw23772step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23772step1 = (fun i j => raw23772step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23772step1 raw23772step0; decide +kernel
      have hl : raw23772step1Labels = raw23772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23772step0 raw23772step0Labels permutation80 hz
    mixedMoment B raw23772step1 raw23772step1Labels = mixedMoment B raw23772step2 raw23772step2Labels := by
      have ha : raw23772step2 = (fun i j => raw23772step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23772step2 raw23772step1; decide +kernel
      have hl : raw23772step2Labels = raw23772step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23772step1 raw23772step1Labels permutation9 permutation4
    mixedMoment B raw23772step2 raw23772step2Labels = mixedMoment B raw23772step3 raw23772step3Labels := by
      have ha : raw23772step3 = -raw23772step2 := by apply Matrix.ext; change ∀ i j, raw23772step3 i j = -(raw23772step2 i j); unfold raw23772step3 raw23772step2; decide +kernel
      have hl : raw23772step3Labels = raw23772step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23772step3 raw23772step3Labels = mixedMoment B raw23772step4 raw23772step4Labels := by
      have ha : raw23772step4 = raw23772step3 := by apply Matrix.ext; unfold raw23772step4 raw23772step3; decide +kernel
      have hl : raw23772step3Labels = labelEmbedding7 ∘ raw23772step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23772step3 raw23772step3Labels raw23772step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4121 node4121Labels := by rfl

def raw23773 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23773step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23773step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23773 raw23773Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw23773 raw23773Labels = mixedMoment B raw23773step0 raw23773step0Labels := by
      have hz : ∀ j, raw23773 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23773step0 = (fun i j => raw23773 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23773step0 raw23773; decide +kernel
      have hl : raw23773step0Labels = raw23773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23773 raw23773Labels permutation434 hz
    mixedMoment B raw23773step0 raw23773step0Labels = mixedMoment B raw23773step1 raw23773step1Labels := by
      have ha : raw23773step1 = (fun i j => raw23773step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23773step1 raw23773step0; decide +kernel
      have hl : raw23773step1Labels = raw23773step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23773step0 raw23773step0Labels permutation39 permutation4
    mixedMoment B raw23773step1 raw23773step1Labels = mixedMoment B raw23773step2 raw23773step2Labels := by
      have ha : raw23773step2 = -raw23773step1 := by apply Matrix.ext; change ∀ i j, raw23773step2 i j = -(raw23773step1 i j); unfold raw23773step2 raw23773step1; decide +kernel
      have hl : raw23773step2Labels = raw23773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23773step2 raw23773step2Labels = mixedMoment B raw23773step3 raw23773step3Labels := by
      have ha : raw23773step3 = raw23773step2 := by apply Matrix.ext; unfold raw23773step3 raw23773step2; decide +kernel
      have hl : raw23773step2Labels = labelEmbedding7 ∘ raw23773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23773step2 raw23773step2Labels raw23773step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw23774 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23774step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23774step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23774step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23774step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23774 raw23774Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw23774 raw23774Labels = mixedMoment B raw23774step0 raw23774step0Labels := by
      have hz : ∀ j, raw23774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23774step0 = (fun i j => raw23774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23774step0 raw23774; decide +kernel
      have hl : raw23774step0Labels = raw23774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23774 raw23774Labels permutation346 hz
    mixedMoment B raw23774step0 raw23774step0Labels = mixedMoment B raw23774step1 raw23774step1Labels := by
      have ha : raw23774step1 = (fun i j => raw23774step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23774step1 raw23774step0; decide +kernel
      have hl : raw23774step1Labels = raw23774step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23774step0 raw23774step0Labels permutation39 permutation4
    mixedMoment B raw23774step1 raw23774step1Labels = mixedMoment B raw23774step2 raw23774step2Labels := by
      have ha : raw23774step2 = -raw23774step1 := by apply Matrix.ext; change ∀ i j, raw23774step2 i j = -(raw23774step1 i j); unfold raw23774step2 raw23774step1; decide +kernel
      have hl : raw23774step2Labels = raw23774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23774step2 raw23774step2Labels = mixedMoment B raw23774step3 raw23774step3Labels := by
      have ha : raw23774step3 = raw23774step2 := by apply Matrix.ext; unfold raw23774step3 raw23774step2; decide +kernel
      have hl : raw23774step2Labels = labelEmbedding7 ∘ raw23774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23774step2 raw23774step2Labels raw23774step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw23775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23775step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23775step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23775step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23775step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23775 raw23775Labels = mixedMoment B node4123 node4123Labels := by
  calc
    mixedMoment B raw23775 raw23775Labels = mixedMoment B raw23775step0 raw23775step0Labels := by
      have hz : ∀ j, raw23775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23775step0 = (fun i j => raw23775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23775step0 raw23775; decide +kernel
      have hl : raw23775step0Labels = raw23775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23775 raw23775Labels permutation434 hz
    mixedMoment B raw23775step0 raw23775step0Labels = mixedMoment B raw23775step1 raw23775step1Labels := by
      have hz : ∀ j, raw23775step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23775step1 = (fun i j => raw23775step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23775step1 raw23775step0; decide +kernel
      have hl : raw23775step1Labels = raw23775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23775step0 raw23775step0Labels permutation80 hz
    mixedMoment B raw23775step1 raw23775step1Labels = mixedMoment B raw23775step2 raw23775step2Labels := by
      have ha : raw23775step2 = (fun i j => raw23775step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23775step2 raw23775step1; decide +kernel
      have hl : raw23775step2Labels = raw23775step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23775step1 raw23775step1Labels permutation8 permutation4
    mixedMoment B raw23775step2 raw23775step2Labels = mixedMoment B raw23775step3 raw23775step3Labels := by
      have ha : raw23775step3 = -raw23775step2 := by apply Matrix.ext; change ∀ i j, raw23775step3 i j = -(raw23775step2 i j); unfold raw23775step3 raw23775step2; decide +kernel
      have hl : raw23775step3Labels = raw23775step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23775step3 raw23775step3Labels = mixedMoment B raw23775step4 raw23775step4Labels := by
      have ha : raw23775step4 = raw23775step3 := by apply Matrix.ext; unfold raw23775step4 raw23775step3; decide +kernel
      have hl : raw23775step3Labels = labelEmbedding7 ∘ raw23775step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23775step3 raw23775step3Labels raw23775step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4123 node4123Labels := by rfl

def raw23776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23776step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23776step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23776 raw23776Labels = mixedMoment B node4214 node4214Labels := by
  calc
    mixedMoment B raw23776 raw23776Labels = mixedMoment B raw23776step0 raw23776step0Labels := by
      have hz : ∀ j, raw23776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23776step0 = (fun i j => raw23776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23776step0 raw23776; decide +kernel
      have hl : raw23776step0Labels = raw23776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23776 raw23776Labels permutation434 hz
    mixedMoment B raw23776step0 raw23776step0Labels = mixedMoment B raw23776step1 raw23776step1Labels := by
      have ha : raw23776step1 = (fun i j => raw23776step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23776step1 raw23776step0; decide +kernel
      have hl : raw23776step1Labels = raw23776step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23776step0 raw23776step0Labels permutation38 permutation4
    mixedMoment B raw23776step1 raw23776step1Labels = mixedMoment B raw23776step2 raw23776step2Labels := by
      have ha : raw23776step2 = -raw23776step1 := by apply Matrix.ext; change ∀ i j, raw23776step2 i j = -(raw23776step1 i j); unfold raw23776step2 raw23776step1; decide +kernel
      have hl : raw23776step2Labels = raw23776step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23776step2 raw23776step2Labels = mixedMoment B raw23776step3 raw23776step3Labels := by
      have ha : raw23776step3 = raw23776step2 := by apply Matrix.ext; unfold raw23776step3 raw23776step2; decide +kernel
      have hl : raw23776step2Labels = labelEmbedding7 ∘ raw23776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23776step2 raw23776step2Labels raw23776step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4214 node4214Labels := by rfl

def raw23777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23777step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw23777step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23777 raw23777Labels = mixedMoment B node4059 node4059Labels := by
  calc
    mixedMoment B raw23777 raw23777Labels = mixedMoment B raw23777step0 raw23777step0Labels := by
      have hz : ∀ j, raw23777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23777step0 = (fun i j => raw23777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23777step0 raw23777; decide +kernel
      have hl : raw23777step0Labels = raw23777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23777 raw23777Labels permutation434 hz
    mixedMoment B raw23777step0 raw23777step0Labels = mixedMoment B raw23777step1 raw23777step1Labels := by
      have hz : ∀ j, raw23777step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23777step1 = (fun i j => raw23777step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23777step1 raw23777step0; decide +kernel
      have hl : raw23777step1Labels = raw23777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23777step0 raw23777step0Labels permutation80 hz
    mixedMoment B raw23777step1 raw23777step1Labels = mixedMoment B raw23777step2 raw23777step2Labels := by
      have hz : ∀ i, raw23777step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23777step2 = (fun i j => raw23777step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23777step2 raw23777step1; decide +kernel
      have hl : raw23777step2Labels = (fun j => raw23777step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23777step1 raw23777step1Labels permutation6 hz
    _ = mixedMoment B node4059 node4059Labels := by rfl

def raw23778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23778step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw23778step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23778step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23778step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23778 raw23778Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23778 raw23778Labels = mixedMoment B raw23778step0 raw23778step0Labels := by
      have hz : ∀ j, raw23778 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23778step0 = (fun i j => raw23778 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23778step0 raw23778; decide +kernel
      have hl : raw23778step0Labels = raw23778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23778 raw23778Labels permutation434 hz
    mixedMoment B raw23778step0 raw23778step0Labels = mixedMoment B raw23778step1 raw23778step1Labels := by
      have hz : ∀ i, raw23778step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23778step1 = (fun i j => raw23778step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23778step1 raw23778step0; decide +kernel
      have hl : raw23778step1Labels = (fun j => raw23778step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23778step0 raw23778step0Labels permutation6 hz
    mixedMoment B raw23778step1 raw23778step1Labels = mixedMoment B raw23778step2 raw23778step2Labels := by
      have ha : raw23778step2 = (fun i j => raw23778step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23778step2 raw23778step1; decide +kernel
      have hl : raw23778step2Labels = raw23778step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23778step1 raw23778step1Labels permutation38 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

def raw23779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23779step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw23779step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23779step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23779step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23779 raw23779Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23779 raw23779Labels = mixedMoment B raw23779step0 raw23779step0Labels := by
      have hz : ∀ j, raw23779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23779step0 = (fun i j => raw23779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23779step0 raw23779; decide +kernel
      have hl : raw23779step0Labels = raw23779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23779 raw23779Labels permutation346 hz
    mixedMoment B raw23779step0 raw23779step0Labels = mixedMoment B raw23779step1 raw23779step1Labels := by
      have hz : ∀ i, raw23779step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23779step1 = (fun i j => raw23779step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23779step1 raw23779step0; decide +kernel
      have hl : raw23779step1Labels = (fun j => raw23779step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23779step0 raw23779step0Labels permutation6 hz
    mixedMoment B raw23779step1 raw23779step1Labels = mixedMoment B raw23779step2 raw23779step2Labels := by
      have ha : raw23779step2 = (fun i j => raw23779step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23779step2 raw23779step1; decide +kernel
      have hl : raw23779step2Labels = raw23779step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23779step1 raw23779step1Labels permutation38 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

def raw23780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23780step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23780step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23780step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23780step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23780step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23780 raw23780Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23780 raw23780Labels = mixedMoment B raw23780step0 raw23780step0Labels := by
      have hz : ∀ j, raw23780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23780step0 = (fun i j => raw23780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23780step0 raw23780; decide +kernel
      have hl : raw23780step0Labels = raw23780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23780 raw23780Labels permutation434 hz
    mixedMoment B raw23780step0 raw23780step0Labels = mixedMoment B raw23780step1 raw23780step1Labels := by
      have hz : ∀ j, raw23780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23780step1 = (fun i j => raw23780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23780step1 raw23780step0; decide +kernel
      have hl : raw23780step1Labels = raw23780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23780step0 raw23780step0Labels permutation80 hz
    mixedMoment B raw23780step1 raw23780step1Labels = mixedMoment B raw23780step2 raw23780step2Labels := by
      have hz : ∀ i, raw23780step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23780step2 = (fun i j => raw23780step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23780step2 raw23780step1; decide +kernel
      have hl : raw23780step2Labels = (fun j => raw23780step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23780step1 raw23780step1Labels permutation6 hz
    mixedMoment B raw23780step2 raw23780step2Labels = mixedMoment B raw23780step3 raw23780step3Labels := by
      have ha : raw23780step3 = (fun i j => raw23780step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23780step3 raw23780step2; decide +kernel
      have hl : raw23780step3Labels = raw23780step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23780step2 raw23780step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw23781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23781step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23781step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw23781step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23781 raw23781Labels = mixedMoment B node4059 node4059Labels := by
  calc
    mixedMoment B raw23781 raw23781Labels = mixedMoment B raw23781step0 raw23781step0Labels := by
      have hz : ∀ j, raw23781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23781step0 = (fun i j => raw23781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23781step0 raw23781; decide +kernel
      have hl : raw23781step0Labels = raw23781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23781 raw23781Labels permutation434 hz
    mixedMoment B raw23781step0 raw23781step0Labels = mixedMoment B raw23781step1 raw23781step1Labels := by
      have hz : ∀ j, raw23781step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23781step1 = (fun i j => raw23781step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23781step1 raw23781step0; decide +kernel
      have hl : raw23781step1Labels = raw23781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23781step0 raw23781step0Labels permutation56 hz
    mixedMoment B raw23781step1 raw23781step1Labels = mixedMoment B raw23781step2 raw23781step2Labels := by
      have hz : ∀ i, raw23781step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23781step2 = (fun i j => raw23781step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23781step2 raw23781step1; decide +kernel
      have hl : raw23781step2Labels = (fun j => raw23781step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23781step1 raw23781step1Labels permutation6 hz
    _ = mixedMoment B node4059 node4059Labels := by rfl

def raw23782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23782step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23782step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23782 raw23782Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23782 raw23782Labels = mixedMoment B raw23782step0 raw23782step0Labels := by
      have hz : ∀ j, raw23782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23782step0 = (fun i j => raw23782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23782step0 raw23782; decide +kernel
      have hl : raw23782step0Labels = raw23782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23782 raw23782Labels permutation434 hz
    mixedMoment B raw23782step0 raw23782step0Labels = mixedMoment B raw23782step1 raw23782step1Labels := by
      have hz : ∀ i, raw23782step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23782step1 = (fun i j => raw23782step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23782step1 raw23782step0; decide +kernel
      have hl : raw23782step1Labels = (fun j => raw23782step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23782step0 raw23782step0Labels permutation6 hz
    _ = mixedMoment B node4065 node4065Labels := by rfl

def raw23783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23783step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw23783step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23783step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23783step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23783 raw23783Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23783 raw23783Labels = mixedMoment B raw23783step0 raw23783step0Labels := by
      have hz : ∀ j, raw23783 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23783step0 = (fun i j => raw23783 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23783step0 raw23783; decide +kernel
      have hl : raw23783step0Labels = raw23783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23783 raw23783Labels permutation265 hz
    mixedMoment B raw23783step0 raw23783step0Labels = mixedMoment B raw23783step1 raw23783step1Labels := by
      have hz : ∀ i, raw23783step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23783step1 = (fun i j => raw23783step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23783step1 raw23783step0; decide +kernel
      have hl : raw23783step1Labels = (fun j => raw23783step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23783step0 raw23783step0Labels permutation6 hz
    mixedMoment B raw23783step1 raw23783step1Labels = mixedMoment B raw23783step2 raw23783step2Labels := by
      have ha : raw23783step2 = (fun i j => raw23783step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23783step2 raw23783step1; decide +kernel
      have hl : raw23783step2Labels = raw23783step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23783step1 raw23783step1Labels permutation38 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

def raw23784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw23784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23784step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw23784step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23784step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23784step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23784 raw23784Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23784 raw23784Labels = mixedMoment B raw23784step0 raw23784step0Labels := by
      have hz : ∀ j, raw23784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23784step0 = (fun i j => raw23784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23784step0 raw23784; decide +kernel
      have hl : raw23784step0Labels = raw23784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23784 raw23784Labels permutation434 hz
    mixedMoment B raw23784step0 raw23784step0Labels = mixedMoment B raw23784step1 raw23784step1Labels := by
      have hz : ∀ j, raw23784step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23784step1 = (fun i j => raw23784step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23784step1 raw23784step0; decide +kernel
      have hl : raw23784step1Labels = raw23784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23784step0 raw23784step0Labels permutation56 hz
    mixedMoment B raw23784step1 raw23784step1Labels = mixedMoment B raw23784step2 raw23784step2Labels := by
      have hz : ∀ i, raw23784step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23784step2 = (fun i j => raw23784step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23784step2 raw23784step1; decide +kernel
      have hl : raw23784step2Labels = (fun j => raw23784step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23784step1 raw23784step1Labels permutation6 hz
    mixedMoment B raw23784step2 raw23784step2Labels = mixedMoment B raw23784step3 raw23784step3Labels := by
      have ha : raw23784step3 = (fun i j => raw23784step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23784step3 raw23784step2; decide +kernel
      have hl : raw23784step3Labels = raw23784step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23784step2 raw23784step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw23785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23785step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23785step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw23785step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23785 raw23785Labels = mixedMoment B node4059 node4059Labels := by
  calc
    mixedMoment B raw23785 raw23785Labels = mixedMoment B raw23785step0 raw23785step0Labels := by
      have hz : ∀ j, raw23785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23785step0 = (fun i j => raw23785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23785step0 raw23785; decide +kernel
      have hl : raw23785step0Labels = raw23785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23785 raw23785Labels permutation346 hz
    mixedMoment B raw23785step0 raw23785step0Labels = mixedMoment B raw23785step1 raw23785step1Labels := by
      have hz : ∀ j, raw23785step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23785step1 = (fun i j => raw23785step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23785step1 raw23785step0; decide +kernel
      have hl : raw23785step1Labels = raw23785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23785step0 raw23785step0Labels permutation56 hz
    mixedMoment B raw23785step1 raw23785step1Labels = mixedMoment B raw23785step2 raw23785step2Labels := by
      have hz : ∀ i, raw23785step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23785step2 = (fun i j => raw23785step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23785step2 raw23785step1; decide +kernel
      have hl : raw23785step2Labels = (fun j => raw23785step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23785step1 raw23785step1Labels permutation6 hz
    _ = mixedMoment B node4059 node4059Labels := by rfl

def raw23786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23786step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23786step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23786 raw23786Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23786 raw23786Labels = mixedMoment B raw23786step0 raw23786step0Labels := by
      have hz : ∀ j, raw23786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23786step0 = (fun i j => raw23786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23786step0 raw23786; decide +kernel
      have hl : raw23786step0Labels = raw23786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23786 raw23786Labels permutation346 hz
    mixedMoment B raw23786step0 raw23786step0Labels = mixedMoment B raw23786step1 raw23786step1Labels := by
      have hz : ∀ i, raw23786step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23786step1 = (fun i j => raw23786step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23786step1 raw23786step0; decide +kernel
      have hl : raw23786step1Labels = (fun j => raw23786step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23786step0 raw23786step0Labels permutation6 hz
    _ = mixedMoment B node4065 node4065Labels := by rfl

def raw23787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw23787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23787step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw23787step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23787 raw23787Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw23787 raw23787Labels = mixedMoment B raw23787step0 raw23787step0Labels := by
      have hz : ∀ j, raw23787 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23787step0 = (fun i j => raw23787 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23787step0 raw23787; decide +kernel
      have hl : raw23787step0Labels = raw23787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23787 raw23787Labels permutation265 hz
    mixedMoment B raw23787step0 raw23787step0Labels = mixedMoment B raw23787step1 raw23787step1Labels := by
      have hz : ∀ i, raw23787step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23787step1 = (fun i j => raw23787step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23787step1 raw23787step0; decide +kernel
      have hl : raw23787step1Labels = (fun j => raw23787step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23787step0 raw23787step0Labels permutation6 hz
    _ = mixedMoment B node4065 node4065Labels := by rfl

def raw23788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23788step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23788step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![3, -3], ![2, -2]]
def raw23788step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23788step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]
def raw23788step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23788 raw23788Labels = mixedMoment B node4061 node4061Labels := by
  calc
    mixedMoment B raw23788 raw23788Labels = mixedMoment B raw23788step0 raw23788step0Labels := by
      have hz : ∀ j, raw23788 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23788step0 = (fun i j => raw23788 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23788step0 raw23788; decide +kernel
      have hl : raw23788step0Labels = raw23788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23788 raw23788Labels permutation434 hz
    mixedMoment B raw23788step0 raw23788step0Labels = mixedMoment B raw23788step1 raw23788step1Labels := by
      have hz : ∀ j, raw23788step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23788step1 = (fun i j => raw23788step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23788step1 raw23788step0; decide +kernel
      have hl : raw23788step1Labels = raw23788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23788step0 raw23788step0Labels permutation80 hz
    mixedMoment B raw23788step1 raw23788step1Labels = mixedMoment B raw23788step2 raw23788step2Labels := by
      have hz : ∀ j, raw23788step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23788step2 = (fun i j => raw23788step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23788step2 raw23788step1; decide +kernel
      have hl : raw23788step2Labels = raw23788step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23788step1 raw23788step1Labels permutation14 hz
    mixedMoment B raw23788step2 raw23788step2Labels = mixedMoment B raw23788step3 raw23788step3Labels := by
      have hz : ∀ i, raw23788step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23788step3 = (fun i j => raw23788step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23788step3 raw23788step2; decide +kernel
      have hl : raw23788step3Labels = (fun j => raw23788step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23788step2 raw23788step2Labels permutation6 hz
    mixedMoment B raw23788step3 raw23788step3Labels = mixedMoment B raw23788step4 raw23788step4Labels := by
      have ha : raw23788step4 = (fun i j => raw23788step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23788step4 raw23788step3; decide +kernel
      have hl : raw23788step4Labels = raw23788step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23788step3 raw23788step3Labels permutation3 permutation0
    _ = mixedMoment B node4061 node4061Labels := by rfl

def raw23789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23789step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23789step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![3, -3], ![2, -2]]
def raw23789step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23789step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw23789step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23789 raw23789Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw23789 raw23789Labels = mixedMoment B raw23789step0 raw23789step0Labels := by
      have hz : ∀ j, raw23789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23789step0 = (fun i j => raw23789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23789step0 raw23789; decide +kernel
      have hl : raw23789step0Labels = raw23789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23789 raw23789Labels permutation434 hz
    mixedMoment B raw23789step0 raw23789step0Labels = mixedMoment B raw23789step1 raw23789step1Labels := by
      have hz : ∀ j, raw23789step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23789step1 = (fun i j => raw23789step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23789step1 raw23789step0; decide +kernel
      have hl : raw23789step1Labels = raw23789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23789step0 raw23789step0Labels permutation80 hz
    mixedMoment B raw23789step1 raw23789step1Labels = mixedMoment B raw23789step2 raw23789step2Labels := by
      have hz : ∀ i, raw23789step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23789step2 = (fun i j => raw23789step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23789step2 raw23789step1; decide +kernel
      have hl : raw23789step2Labels = (fun j => raw23789step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23789step1 raw23789step1Labels permutation6 hz
    mixedMoment B raw23789step2 raw23789step2Labels = mixedMoment B raw23789step3 raw23789step3Labels := by
      have ha : raw23789step3 = (fun i j => raw23789step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23789step3 raw23789step2; decide +kernel
      have hl : raw23789step3Labels = raw23789step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23789step2 raw23789step2Labels permutation9 permutation0
    _ = mixedMoment B node4067 node4067Labels := by rfl

def raw23790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23790step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![3, -3], ![2, -2]]
def raw23790step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23790step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw23790step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23790 raw23790Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw23790 raw23790Labels = mixedMoment B raw23790step0 raw23790step0Labels := by
      have hz : ∀ j, raw23790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23790step0 = (fun i j => raw23790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23790step0 raw23790; decide +kernel
      have hl : raw23790step0Labels = raw23790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23790 raw23790Labels permutation434 hz
    mixedMoment B raw23790step0 raw23790step0Labels = mixedMoment B raw23790step1 raw23790step1Labels := by
      have hz : ∀ j, raw23790step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23790step1 = (fun i j => raw23790step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23790step1 raw23790step0; decide +kernel
      have hl : raw23790step1Labels = raw23790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23790step0 raw23790step0Labels permutation56 hz
    mixedMoment B raw23790step1 raw23790step1Labels = mixedMoment B raw23790step2 raw23790step2Labels := by
      have hz : ∀ i, raw23790step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23790step2 = (fun i j => raw23790step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23790step2 raw23790step1; decide +kernel
      have hl : raw23790step2Labels = (fun j => raw23790step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23790step1 raw23790step1Labels permutation6 hz
    mixedMoment B raw23790step2 raw23790step2Labels = mixedMoment B raw23790step3 raw23790step3Labels := by
      have ha : raw23790step3 = (fun i j => raw23790step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23790step3 raw23790step2; decide +kernel
      have hl : raw23790step3Labels = raw23790step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23790step2 raw23790step2Labels permutation9 permutation0
    _ = mixedMoment B node4067 node4067Labels := by rfl

def raw23791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw23791step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23791step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![3, -3], ![2, -2]]
def raw23791step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23791step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw23791step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23791 raw23791Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw23791 raw23791Labels = mixedMoment B raw23791step0 raw23791step0Labels := by
      have hz : ∀ j, raw23791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23791step0 = (fun i j => raw23791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23791step0 raw23791; decide +kernel
      have hl : raw23791step0Labels = raw23791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23791 raw23791Labels permutation346 hz
    mixedMoment B raw23791step0 raw23791step0Labels = mixedMoment B raw23791step1 raw23791step1Labels := by
      have hz : ∀ j, raw23791step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23791step1 = (fun i j => raw23791step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23791step1 raw23791step0; decide +kernel
      have hl : raw23791step1Labels = raw23791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23791step0 raw23791step0Labels permutation56 hz
    mixedMoment B raw23791step1 raw23791step1Labels = mixedMoment B raw23791step2 raw23791step2Labels := by
      have hz : ∀ i, raw23791step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23791step2 = (fun i j => raw23791step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23791step2 raw23791step1; decide +kernel
      have hl : raw23791step2Labels = (fun j => raw23791step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23791step1 raw23791step1Labels permutation6 hz
    mixedMoment B raw23791step2 raw23791step2Labels = mixedMoment B raw23791step3 raw23791step3Labels := by
      have ha : raw23791step3 = (fun i j => raw23791step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23791step3 raw23791step2; decide +kernel
      have hl : raw23791step3Labels = raw23791step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23791step2 raw23791step2Labels permutation9 permutation0
    _ = mixedMoment B node4067 node4067Labels := by rfl

def raw23792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![3, -3, 0], ![1, -1, 0]]
def raw23792step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23792step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![3, -3], ![1, -1]]
def raw23792step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23792step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw23792step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23792 raw23792Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw23792 raw23792Labels = mixedMoment B raw23792step0 raw23792step0Labels := by
      have hz : ∀ j, raw23792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23792step0 = (fun i j => raw23792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23792step0 raw23792; decide +kernel
      have hl : raw23792step0Labels = raw23792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23792 raw23792Labels permutation434 hz
    mixedMoment B raw23792step0 raw23792step0Labels = mixedMoment B raw23792step1 raw23792step1Labels := by
      have hz : ∀ j, raw23792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23792step1 = (fun i j => raw23792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23792step1 raw23792step0; decide +kernel
      have hl : raw23792step1Labels = raw23792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23792step0 raw23792step0Labels permutation80 hz
    mixedMoment B raw23792step1 raw23792step1Labels = mixedMoment B raw23792step2 raw23792step2Labels := by
      have hz : ∀ j, raw23792step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23792step2 = (fun i j => raw23792step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23792step2 raw23792step1; decide +kernel
      have hl : raw23792step2Labels = raw23792step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23792step1 raw23792step1Labels permutation14 hz
    mixedMoment B raw23792step2 raw23792step2Labels = mixedMoment B raw23792step3 raw23792step3Labels := by
      have hz : ∀ i, raw23792step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw23792step3 = (fun i j => raw23792step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw23792step3 raw23792step2; decide +kernel
      have hl : raw23792step3Labels = (fun j => raw23792step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23792step2 raw23792step2Labels permutation6 hz
    mixedMoment B raw23792step3 raw23792step3Labels = mixedMoment B raw23792step4 raw23792step4Labels := by
      have ha : raw23792step4 = (fun i j => raw23792step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23792step4 raw23792step3; decide +kernel
      have hl : raw23792step4Labels = raw23792step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23792step3 raw23792step3Labels permutation3 permutation0
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw23793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23793step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23793step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23793 raw23793Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw23793 raw23793Labels = mixedMoment B raw23793step0 raw23793step0Labels := by
      have hz : ∀ j, raw23793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23793step0 = (fun i j => raw23793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23793step0 raw23793; decide +kernel
      have hl : raw23793step0Labels = raw23793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23793 raw23793Labels permutation346 hz
    mixedMoment B raw23793step0 raw23793step0Labels = mixedMoment B raw23793step1 raw23793step1Labels := by
      have hz : ∀ j, raw23793step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23793step1 = (fun i j => raw23793step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23793step1 raw23793step0; decide +kernel
      have hl : raw23793step1Labels = raw23793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23793step0 raw23793step0Labels permutation56 hz
    mixedMoment B raw23793step1 raw23793step1Labels = mixedMoment B raw23793step2 raw23793step2Labels := by
      have ha : raw23793step2 = (fun i j => raw23793step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23793step2 raw23793step1; decide +kernel
      have hl : raw23793step2Labels = raw23793step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23793step1 raw23793step1Labels permutation9 permutation4
    mixedMoment B raw23793step2 raw23793step2Labels = mixedMoment B raw23793step3 raw23793step3Labels := by
      have ha : raw23793step3 = -raw23793step2 := by apply Matrix.ext; change ∀ i j, raw23793step3 i j = -(raw23793step2 i j); unfold raw23793step3 raw23793step2; decide +kernel
      have hl : raw23793step3Labels = raw23793step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw23794 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23794 raw23794Labels = mixedMoment B node3022 node3022Labels := by
  calc
    mixedMoment B raw23794 raw23794Labels = mixedMoment B raw23794step0 raw23794step0Labels := by
      have hz : ∀ j, raw23794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23794step0 = (fun i j => raw23794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23794step0 raw23794; decide +kernel
      have hl : raw23794step0Labels = raw23794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23794 raw23794Labels permutation346 hz
    mixedMoment B raw23794step0 raw23794step0Labels = mixedMoment B raw23794step1 raw23794step1Labels := by
      have ha : raw23794step1 = (fun i j => raw23794step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23794step1 raw23794step0; decide +kernel
      have hl : raw23794step1Labels = raw23794step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23794step0 raw23794step0Labels permutation127 permutation4
    _ = mixedMoment B node3022 node3022Labels := by rfl

def raw23795 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23795 raw23795Labels = mixedMoment B node3022 node3022Labels := by
  calc
    mixedMoment B raw23795 raw23795Labels = mixedMoment B raw23795step0 raw23795step0Labels := by
      have hz : ∀ j, raw23795 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23795step0 = (fun i j => raw23795 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23795step0 raw23795; decide +kernel
      have hl : raw23795step0Labels = raw23795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23795 raw23795Labels permutation265 hz
    mixedMoment B raw23795step0 raw23795step0Labels = mixedMoment B raw23795step1 raw23795step1Labels := by
      have ha : raw23795step1 = (fun i j => raw23795step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23795step1 raw23795step0; decide +kernel
      have hl : raw23795step1Labels = raw23795step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23795step0 raw23795step0Labels permutation127 permutation4
    _ = mixedMoment B node3022 node3022Labels := by rfl

def raw23796 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw23796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23796step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw23796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23796 raw23796Labels = mixedMoment B node3049 node3049Labels := by
  calc
    mixedMoment B raw23796 raw23796Labels = mixedMoment B raw23796step0 raw23796step0Labels := by
      have hz : ∀ j, raw23796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23796step0 = (fun i j => raw23796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23796step0 raw23796; decide +kernel
      have hl : raw23796step0Labels = raw23796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23796 raw23796Labels permutation346 hz
    mixedMoment B raw23796step0 raw23796step0Labels = mixedMoment B raw23796step1 raw23796step1Labels := by
      have hz : ∀ j, raw23796step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23796step1 = (fun i j => raw23796step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23796step1 raw23796step0; decide +kernel
      have hl : raw23796step1Labels = raw23796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23796step0 raw23796step0Labels permutation56 hz
    mixedMoment B raw23796step1 raw23796step1Labels = mixedMoment B raw23796step2 raw23796step2Labels := by
      have ha : raw23796step2 = (fun i j => raw23796step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23796step2 raw23796step1; decide +kernel
      have hl : raw23796step2Labels = raw23796step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23796step1 raw23796step1Labels permutation25 permutation4
    _ = mixedMoment B node3049 node3049Labels := by rfl

def raw23797 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23797step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23797step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23797 raw23797Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw23797 raw23797Labels = mixedMoment B raw23797step0 raw23797step0Labels := by
      have hz : ∀ j, raw23797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23797step0 = (fun i j => raw23797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23797step0 raw23797; decide +kernel
      have hl : raw23797step0Labels = raw23797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23797 raw23797Labels permutation346 hz
    mixedMoment B raw23797step0 raw23797step0Labels = mixedMoment B raw23797step1 raw23797step1Labels := by
      have hz : ∀ j, raw23797step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23797step1 = (fun i j => raw23797step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23797step1 raw23797step0; decide +kernel
      have hl : raw23797step1Labels = raw23797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23797step0 raw23797step0Labels permutation56 hz
    mixedMoment B raw23797step1 raw23797step1Labels = mixedMoment B raw23797step2 raw23797step2Labels := by
      have ha : raw23797step2 = (fun i j => raw23797step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23797step2 raw23797step1; decide +kernel
      have hl : raw23797step2Labels = raw23797step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23797step1 raw23797step1Labels permutation10 permutation2
    mixedMoment B raw23797step2 raw23797step2Labels = mixedMoment B raw23797step3 raw23797step3Labels := by
      have ha : raw23797step3 = -raw23797step2 := by apply Matrix.ext; change ∀ i j, raw23797step3 i j = -(raw23797step2 i j); unfold raw23797step3 raw23797step2; decide +kernel
      have hl : raw23797step3Labels = raw23797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw23798 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw23798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw23798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw23798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23798step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw23798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23798 raw23798Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw23798 raw23798Labels = mixedMoment B raw23798step0 raw23798step0Labels := by
      have hz : ∀ j, raw23798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23798step0 = (fun i j => raw23798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23798step0 raw23798; decide +kernel
      have hl : raw23798step0Labels = raw23798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23798 raw23798Labels permutation346 hz
    mixedMoment B raw23798step0 raw23798step0Labels = mixedMoment B raw23798step1 raw23798step1Labels := by
      have hz : ∀ j, raw23798step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23798step1 = (fun i j => raw23798step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23798step1 raw23798step0; decide +kernel
      have hl : raw23798step1Labels = raw23798step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23798step0 raw23798step0Labels permutation56 hz
    mixedMoment B raw23798step1 raw23798step1Labels = mixedMoment B raw23798step2 raw23798step2Labels := by
      have ha : raw23798step2 = (fun i j => raw23798step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23798step2 raw23798step1; decide +kernel
      have hl : raw23798step2Labels = raw23798step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23798step1 raw23798step1Labels permutation29 permutation2
    _ = mixedMoment B node2521 node2521Labels := by rfl

def raw23799 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw23799Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23799step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw23799step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23799step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw23799step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23799step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw23799step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23799 raw23799Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23799 raw23799Labels = mixedMoment B raw23799step0 raw23799step0Labels := by
      have hz : ∀ j, raw23799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23799step0 = (fun i j => raw23799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23799step0 raw23799; decide +kernel
      have hl : raw23799step0Labels = raw23799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799 raw23799Labels permutation346 hz
    mixedMoment B raw23799step0 raw23799step0Labels = mixedMoment B raw23799step1 raw23799step1Labels := by
      have hz : ∀ j, raw23799step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23799step1 = (fun i j => raw23799step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23799step1 raw23799step0; decide +kernel
      have hl : raw23799step1Labels = raw23799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799step0 raw23799step0Labels permutation56 hz
    mixedMoment B raw23799step1 raw23799step1Labels = mixedMoment B raw23799step2 raw23799step2Labels := by
      have ha : raw23799step2 = -raw23799step1 := by apply Matrix.ext; change ∀ i j, raw23799step2 i j = -(raw23799step1 i j); unfold raw23799step2 raw23799step1; decide +kernel
      have hl : raw23799step2Labels = raw23799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw23800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23800 raw23800Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw23800 raw23800Labels = mixedMoment B raw23800step0 raw23800step0Labels := by
      have hz : ∀ j, raw23800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23800step0 = (fun i j => raw23800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23800step0 raw23800; decide +kernel
      have hl : raw23800step0Labels = raw23800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23800 raw23800Labels permutation346 hz
    mixedMoment B raw23800step0 raw23800step0Labels = mixedMoment B raw23800step1 raw23800step1Labels := by
      have ha : raw23800step1 = (fun i j => raw23800step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23800step1 raw23800step0; decide +kernel
      have hl : raw23800step1Labels = raw23800step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23800step0 raw23800step0Labels permutation42 permutation4
    mixedMoment B raw23800step1 raw23800step1Labels = mixedMoment B raw23800step2 raw23800step2Labels := by
      have ha : raw23800step2 = -raw23800step1 := by apply Matrix.ext; change ∀ i j, raw23800step2 i j = -(raw23800step1 i j); unfold raw23800step2 raw23800step1; decide +kernel
      have hl : raw23800step2Labels = raw23800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw23801 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23801 raw23801Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw23801 raw23801Labels = mixedMoment B raw23801step0 raw23801step0Labels := by
      have hz : ∀ j, raw23801 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23801step0 = (fun i j => raw23801 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23801step0 raw23801; decide +kernel
      have hl : raw23801step0Labels = raw23801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23801 raw23801Labels permutation265 hz
    mixedMoment B raw23801step0 raw23801step0Labels = mixedMoment B raw23801step1 raw23801step1Labels := by
      have ha : raw23801step1 = (fun i j => raw23801step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23801step1 raw23801step0; decide +kernel
      have hl : raw23801step1Labels = raw23801step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23801step0 raw23801step0Labels permutation42 permutation4
    mixedMoment B raw23801step1 raw23801step1Labels = mixedMoment B raw23801step2 raw23801step2Labels := by
      have ha : raw23801step2 = -raw23801step1 := by apply Matrix.ext; change ∀ i j, raw23801step2 i j = -(raw23801step1 i j); unfold raw23801step2 raw23801step1; decide +kernel
      have hl : raw23801step2Labels = raw23801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw23802 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw23802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw23802step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23802 raw23802Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw23802 raw23802Labels = mixedMoment B raw23802step0 raw23802step0Labels := by
      have hz : ∀ j, raw23802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23802step0 = (fun i j => raw23802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23802step0 raw23802; decide +kernel
      have hl : raw23802step0Labels = raw23802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23802 raw23802Labels permutation346 hz
    mixedMoment B raw23802step0 raw23802step0Labels = mixedMoment B raw23802step1 raw23802step1Labels := by
      have hz : ∀ j, raw23802step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23802step1 = (fun i j => raw23802step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23802step1 raw23802step0; decide +kernel
      have hl : raw23802step1Labels = raw23802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23802step0 raw23802step0Labels permutation56 hz
    mixedMoment B raw23802step1 raw23802step1Labels = mixedMoment B raw23802step2 raw23802step2Labels := by
      have ha : raw23802step2 = (fun i j => raw23802step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23802step2 raw23802step1; decide +kernel
      have hl : raw23802step2Labels = raw23802step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23802step1 raw23802step1Labels permutation12 permutation4
    mixedMoment B raw23802step2 raw23802step2Labels = mixedMoment B raw23802step3 raw23802step3Labels := by
      have ha : raw23802step3 = -raw23802step2 := by apply Matrix.ext; change ∀ i j, raw23802step3 i j = -(raw23802step2 i j); unfold raw23802step3 raw23802step2; decide +kernel
      have hl : raw23802step3Labels = raw23802step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw23803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23803step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23803 raw23803Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw23803 raw23803Labels = mixedMoment B raw23803step0 raw23803step0Labels := by
      have hz : ∀ j, raw23803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23803step0 = (fun i j => raw23803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23803step0 raw23803; decide +kernel
      have hl : raw23803step0Labels = raw23803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23803 raw23803Labels permutation346 hz
    mixedMoment B raw23803step0 raw23803step0Labels = mixedMoment B raw23803step1 raw23803step1Labels := by
      have hz : ∀ j, raw23803step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23803step1 = (fun i j => raw23803step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23803step1 raw23803step0; decide +kernel
      have hl : raw23803step1Labels = raw23803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23803step0 raw23803step0Labels permutation56 hz
    mixedMoment B raw23803step1 raw23803step1Labels = mixedMoment B raw23803step2 raw23803step2Labels := by
      have ha : raw23803step2 = (fun i j => raw23803step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23803step2 raw23803step1; decide +kernel
      have hl : raw23803step2Labels = raw23803step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23803step1 raw23803step1Labels permutation9 permutation4
    mixedMoment B raw23803step2 raw23803step2Labels = mixedMoment B raw23803step3 raw23803step3Labels := by
      have ha : raw23803step3 = -raw23803step2 := by apply Matrix.ext; change ∀ i j, raw23803step3 i j = -(raw23803step2 i j); unfold raw23803step3 raw23803step2; decide +kernel
      have hl : raw23803step3Labels = raw23803step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw23804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23804 raw23804Labels = mixedMoment B node604 node604Labels := by
  calc
    mixedMoment B raw23804 raw23804Labels = mixedMoment B raw23804step0 raw23804step0Labels := by
      have hz : ∀ j, raw23804 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23804step0 = (fun i j => raw23804 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23804step0 raw23804; decide +kernel
      have hl : raw23804step0Labels = raw23804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23804 raw23804Labels permutation265 hz
    mixedMoment B raw23804step0 raw23804step0Labels = mixedMoment B raw23804step1 raw23804step1Labels := by
      have ha : raw23804step1 = (fun i j => raw23804step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23804step1 raw23804step0; decide +kernel
      have hl : raw23804step1Labels = raw23804step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23804step0 raw23804step0Labels permutation38 permutation2
    _ = mixedMoment B node604 node604Labels := by rfl

def raw23805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23805 raw23805Labels = mixedMoment B node923 node923Labels := by
  calc
    mixedMoment B raw23805 raw23805Labels = mixedMoment B raw23805step0 raw23805step0Labels := by
      have ha : raw23805step0 = (fun i j => raw23805 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23805step0 raw23805; decide +kernel
      have hl : raw23805step0Labels = raw23805Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23805 raw23805Labels permutation158 permutation2
    _ = mixedMoment B node923 node923Labels := by rfl

def raw23806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23806 raw23806Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw23806 raw23806Labels = mixedMoment B raw23806step0 raw23806step0Labels := by
      have hz : ∀ j, raw23806 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23806step0 = (fun i j => raw23806 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23806step0 raw23806; decide +kernel
      have hl : raw23806step0Labels = raw23806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23806 raw23806Labels permutation265 hz
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw23807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23807 raw23807Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw23807 raw23807Labels = mixedMoment B raw23807step0 raw23807step0Labels := by
      have hz : ∀ j, raw23807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23807step0 = (fun i j => raw23807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23807step0 raw23807; decide +kernel
      have hl : raw23807step0Labels = raw23807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23807 raw23807Labels permutation434 hz
    mixedMoment B raw23807step0 raw23807step0Labels = mixedMoment B raw23807step1 raw23807step1Labels := by
      have hz : ∀ j, raw23807step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23807step1 = (fun i j => raw23807step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23807step1 raw23807step0; decide +kernel
      have hl : raw23807step1Labels = raw23807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23807step0 raw23807step0Labels permutation56 hz
    _ = mixedMoment B node1087 node1087Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
