import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37504 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37504 raw37504Labels = mixedMoment B node1488 node1488Labels := by
  calc
    mixedMoment B raw37504 raw37504Labels = mixedMoment B raw37504step0 raw37504step0Labels := by
      have ha : raw37504step0 = (fun i j => raw37504 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37504step0 raw37504; decide +kernel
      have hl : raw37504step0Labels = raw37504Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37504 raw37504Labels permutation164 permutation4
    mixedMoment B raw37504step0 raw37504step0Labels = mixedMoment B raw37504step1 raw37504step1Labels := by
      have ha : raw37504step1 = -raw37504step0 := by apply Matrix.ext; change ∀ i j, raw37504step1 i j = -(raw37504step0 i j); unfold raw37504step1 raw37504step0; decide +kernel
      have hl : raw37504step1Labels = raw37504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1488 node1488Labels := by rfl

def raw37505 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw37505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw37505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37505 raw37505Labels = mixedMoment B node1498 node1498Labels := by
  calc
    mixedMoment B raw37505 raw37505Labels = mixedMoment B raw37505step0 raw37505step0Labels := by
      have hz : ∀ j, raw37505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37505step0 = (fun i j => raw37505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37505step0 raw37505; decide +kernel
      have hl : raw37505step0Labels = raw37505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37505 raw37505Labels permutation265 hz
    mixedMoment B raw37505step0 raw37505step0Labels = mixedMoment B raw37505step1 raw37505step1Labels := by
      have ha : raw37505step1 = (fun i j => raw37505step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37505step1 raw37505step0; decide +kernel
      have hl : raw37505step1Labels = raw37505step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37505step0 raw37505step0Labels permutation44 permutation4
    mixedMoment B raw37505step1 raw37505step1Labels = mixedMoment B raw37505step2 raw37505step2Labels := by
      have ha : raw37505step2 = -raw37505step1 := by apply Matrix.ext; change ∀ i j, raw37505step2 i j = -(raw37505step1 i j); unfold raw37505step2 raw37505step1; decide +kernel
      have hl : raw37505step2Labels = raw37505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1498 node1498Labels := by rfl

def raw37506 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw37506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37506 raw37506Labels = mixedMoment B node656 node656Labels := by
  calc
    mixedMoment B raw37506 raw37506Labels = mixedMoment B raw37506step0 raw37506step0Labels := by
      have ha : raw37506step0 = (fun i j => raw37506 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37506step0 raw37506; decide +kernel
      have hl : raw37506step0Labels = raw37506Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37506 raw37506Labels permutation212 permutation4
    mixedMoment B raw37506step0 raw37506step0Labels = mixedMoment B raw37506step1 raw37506step1Labels := by
      have ha : raw37506step1 = -raw37506step0 := by apply Matrix.ext; change ∀ i j, raw37506step1 i j = -(raw37506step0 i j); unfold raw37506step1 raw37506step0; decide +kernel
      have hl : raw37506step1Labels = raw37506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node656 node656Labels := by rfl

def raw37507 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw37507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw37507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37507 raw37507Labels = mixedMoment B node660 node660Labels := by
  calc
    mixedMoment B raw37507 raw37507Labels = mixedMoment B raw37507step0 raw37507step0Labels := by
      have hz : ∀ j, raw37507 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37507step0 = (fun i j => raw37507 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37507step0 raw37507; decide +kernel
      have hl : raw37507step0Labels = raw37507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37507 raw37507Labels permutation265 hz
    mixedMoment B raw37507step0 raw37507step0Labels = mixedMoment B raw37507step1 raw37507step1Labels := by
      have ha : raw37507step1 = (fun i j => raw37507step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37507step1 raw37507step0; decide +kernel
      have hl : raw37507step1Labels = raw37507step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37507step0 raw37507step0Labels permutation40 permutation4
    mixedMoment B raw37507step1 raw37507step1Labels = mixedMoment B raw37507step2 raw37507step2Labels := by
      have ha : raw37507step2 = -raw37507step1 := by apply Matrix.ext; change ∀ i j, raw37507step2 i j = -(raw37507step1 i j); unfold raw37507step2 raw37507step1; decide +kernel
      have hl : raw37507step2Labels = raw37507step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node660 node660Labels := by rfl

def raw37508 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw37508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw37508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37508 raw37508Labels = mixedMoment B node667 node667Labels := by
  calc
    mixedMoment B raw37508 raw37508Labels = mixedMoment B raw37508step0 raw37508step0Labels := by
      have hz : ∀ j, raw37508 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37508step0 = (fun i j => raw37508 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37508step0 raw37508; decide +kernel
      have hl : raw37508step0Labels = raw37508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37508 raw37508Labels permutation265 hz
    mixedMoment B raw37508step0 raw37508step0Labels = mixedMoment B raw37508step1 raw37508step1Labels := by
      have ha : raw37508step1 = (fun i j => raw37508step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37508step1 raw37508step0; decide +kernel
      have hl : raw37508step1Labels = raw37508step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37508step0 raw37508step0Labels permutation38 permutation4
    mixedMoment B raw37508step1 raw37508step1Labels = mixedMoment B raw37508step2 raw37508step2Labels := by
      have ha : raw37508step2 = -raw37508step1 := by apply Matrix.ext; change ∀ i j, raw37508step2 i j = -(raw37508step1 i j); unfold raw37508step2 raw37508step1; decide +kernel
      have hl : raw37508step2Labels = raw37508step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node667 node667Labels := by rfl

def raw37509 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw37509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw37509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw37509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw37509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37509 raw37509Labels = mixedMoment B node659 node659Labels := by
  calc
    mixedMoment B raw37509 raw37509Labels = mixedMoment B raw37509step0 raw37509step0Labels := by
      have hz : ∀ j, raw37509 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37509step0 = (fun i j => raw37509 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37509step0 raw37509; decide +kernel
      have hl : raw37509step0Labels = raw37509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37509 raw37509Labels permutation265 hz
    mixedMoment B raw37509step0 raw37509step0Labels = mixedMoment B raw37509step1 raw37509step1Labels := by
      have ha : raw37509step1 = (fun i j => raw37509step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37509step1 raw37509step0; decide +kernel
      have hl : raw37509step1Labels = raw37509step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37509step0 raw37509step0Labels permutation40 permutation4
    mixedMoment B raw37509step1 raw37509step1Labels = mixedMoment B raw37509step2 raw37509step2Labels := by
      have ha : raw37509step2 = -raw37509step1 := by apply Matrix.ext; change ∀ i j, raw37509step2 i j = -(raw37509step1 i j); unfold raw37509step2 raw37509step1; decide +kernel
      have hl : raw37509step2Labels = raw37509step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node659 node659Labels := by rfl

def raw37510 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 5, -5], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, 0, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 0, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37510 raw37510Labels = mixedMoment B node534 node534Labels := by
  calc
    mixedMoment B raw37510 raw37510Labels = mixedMoment B raw37510step0 raw37510step0Labels := by
      have ha : raw37510step0 = (fun i j => raw37510 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37510step0 raw37510; decide +kernel
      have hl : raw37510step0Labels = raw37510Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37510 raw37510Labels permutation152 permutation4
    mixedMoment B raw37510step0 raw37510step0Labels = mixedMoment B raw37510step1 raw37510step1Labels := by
      have ha : raw37510step1 = -raw37510step0 := by apply Matrix.ext; change ∀ i j, raw37510step1 i j = -(raw37510step0 i j); unfold raw37510step1 raw37510step0; decide +kernel
      have hl : raw37510step1Labels = raw37510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node534 node534Labels := by rfl

def raw37511 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37511 raw37511Labels = mixedMoment B node662 node662Labels := by
  calc
    mixedMoment B raw37511 raw37511Labels = mixedMoment B raw37511step0 raw37511step0Labels := by
      have ha : raw37511step0 = (fun i j => raw37511 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37511step0 raw37511; decide +kernel
      have hl : raw37511step0Labels = raw37511Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37511 raw37511Labels permutation176 permutation4
    mixedMoment B raw37511step0 raw37511step0Labels = mixedMoment B raw37511step1 raw37511step1Labels := by
      have ha : raw37511step1 = -raw37511step0 := by apply Matrix.ext; change ∀ i j, raw37511step1 i j = -(raw37511step0 i j); unfold raw37511step1 raw37511step0; decide +kernel
      have hl : raw37511step1Labels = raw37511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node662 node662Labels := by rfl

def raw37512 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37512 raw37512Labels = mixedMoment B node662 node662Labels := by
  calc
    mixedMoment B raw37512 raw37512Labels = mixedMoment B raw37512step0 raw37512step0Labels := by
      have ha : raw37512step0 = (fun i j => raw37512 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37512step0 raw37512; decide +kernel
      have hl : raw37512step0Labels = raw37512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37512 raw37512Labels permutation200 permutation4
    mixedMoment B raw37512step0 raw37512step0Labels = mixedMoment B raw37512step1 raw37512step1Labels := by
      have ha : raw37512step1 = -raw37512step0 := by apply Matrix.ext; change ∀ i j, raw37512step1 i j = -(raw37512step0 i j); unfold raw37512step1 raw37512step0; decide +kernel
      have hl : raw37512step1Labels = raw37512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node662 node662Labels := by rfl

def raw37513 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw37513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37513 raw37513Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37513 raw37513Labels = mixedMoment B raw37513step0 raw37513step0Labels := by
      have ha : raw37513step0 = (fun i j => raw37513 (permutation240 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37513step0 raw37513; decide +kernel
      have hl : raw37513step0Labels = raw37513Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37513 raw37513Labels permutation240 permutation2
    mixedMoment B raw37513step0 raw37513step0Labels = mixedMoment B raw37513step1 raw37513step1Labels := by
      have ha : raw37513step1 = -raw37513step0 := by apply Matrix.ext; change ∀ i j, raw37513step1 i j = -(raw37513step0 i j); unfold raw37513step1 raw37513step0; decide +kernel
      have hl : raw37513step1Labels = raw37513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw37514 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw37514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37514 raw37514Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37514 raw37514Labels = mixedMoment B raw37514step0 raw37514step0Labels := by
      have ha : raw37514step0 = (fun i j => raw37514 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37514step0 raw37514; decide +kernel
      have hl : raw37514step0Labels = raw37514Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37514 raw37514Labels permutation182 permutation4
    mixedMoment B raw37514step0 raw37514step0Labels = mixedMoment B raw37514step1 raw37514step1Labels := by
      have ha : raw37514step1 = -raw37514step0 := by apply Matrix.ext; change ∀ i j, raw37514step1 i j = -(raw37514step0 i j); unfold raw37514step1 raw37514step0; decide +kernel
      have hl : raw37514step1Labels = raw37514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw37515 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw37515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37515 raw37515Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37515 raw37515Labels = mixedMoment B raw37515step0 raw37515step0Labels := by
      have ha : raw37515step0 = (fun i j => raw37515 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37515step0 raw37515; decide +kernel
      have hl : raw37515step0Labels = raw37515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37515 raw37515Labels permutation158 permutation4
    mixedMoment B raw37515step0 raw37515step0Labels = mixedMoment B raw37515step1 raw37515step1Labels := by
      have ha : raw37515step1 = -raw37515step0 := by apply Matrix.ext; change ∀ i j, raw37515step1 i j = -(raw37515step0 i j); unfold raw37515step1 raw37515step0; decide +kernel
      have hl : raw37515step1Labels = raw37515step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw37516 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw37516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37516 raw37516Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37516 raw37516Labels = mixedMoment B raw37516step0 raw37516step0Labels := by
      have ha : raw37516step0 = (fun i j => raw37516 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37516step0 raw37516; decide +kernel
      have hl : raw37516step0Labels = raw37516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37516 raw37516Labels permutation152 permutation4
    mixedMoment B raw37516step0 raw37516step0Labels = mixedMoment B raw37516step1 raw37516step1Labels := by
      have ha : raw37516step1 = -raw37516step0 := by apply Matrix.ext; change ∀ i j, raw37516step1 i j = -(raw37516step0 i j); unfold raw37516step1 raw37516step0; decide +kernel
      have hl : raw37516step1Labels = raw37516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw37517 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw37517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37517 raw37517Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw37517 raw37517Labels = mixedMoment B raw37517step0 raw37517step0Labels := by
      have ha : raw37517step0 = (fun i j => raw37517 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37517step0 raw37517; decide +kernel
      have hl : raw37517step0Labels = raw37517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37517 raw37517Labels permutation153 permutation4
    mixedMoment B raw37517step0 raw37517step0Labels = mixedMoment B raw37517step1 raw37517step1Labels := by
      have ha : raw37517step1 = -raw37517step0 := by apply Matrix.ext; change ∀ i j, raw37517step1 i j = -(raw37517step0 i j); unfold raw37517step1 raw37517step0; decide +kernel
      have hl : raw37517step1Labels = raw37517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1502 node1502Labels := by rfl

def raw37518 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw37518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37518 raw37518Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw37518 raw37518Labels = mixedMoment B raw37518step0 raw37518step0Labels := by
      have ha : raw37518step0 = (fun i j => raw37518 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37518step0 raw37518; decide +kernel
      have hl : raw37518step0Labels = raw37518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37518 raw37518Labels permutation152 permutation4
    mixedMoment B raw37518step0 raw37518step0Labels = mixedMoment B raw37518step1 raw37518step1Labels := by
      have ha : raw37518step1 = -raw37518step0 := by apply Matrix.ext; change ∀ i j, raw37518step1 i j = -(raw37518step0 i j); unfold raw37518step1 raw37518step0; decide +kernel
      have hl : raw37518step1Labels = raw37518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1502 node1502Labels := by rfl

def raw37519 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw37519Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37519step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw37519step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37519 raw37519Labels = mixedMoment B node4056 node4056Labels := by
  calc
    mixedMoment B raw37519 raw37519Labels = mixedMoment B raw37519step0 raw37519step0Labels := by
      have ha : raw37519step0 = -raw37519 := by apply Matrix.ext; change ∀ i j, raw37519step0 i j = -(raw37519 i j); unfold raw37519step0 raw37519; decide +kernel
      have hl : raw37519step0Labels = raw37519Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4056 node4056Labels := by rfl

def raw37520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw37520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37520 raw37520Labels = mixedMoment B node666 node666Labels := by
  calc
    mixedMoment B raw37520 raw37520Labels = mixedMoment B raw37520step0 raw37520step0Labels := by
      have ha : raw37520step0 = (fun i j => raw37520 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37520step0 raw37520; decide +kernel
      have hl : raw37520step0Labels = raw37520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37520 raw37520Labels permutation246 permutation4
    mixedMoment B raw37520step0 raw37520step0Labels = mixedMoment B raw37520step1 raw37520step1Labels := by
      have ha : raw37520step1 = -raw37520step0 := by apply Matrix.ext; change ∀ i j, raw37520step1 i j = -(raw37520step0 i j); unfold raw37520step1 raw37520step0; decide +kernel
      have hl : raw37520step1Labels = raw37520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node666 node666Labels := by rfl

def raw37521 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw37521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37521 raw37521Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37521 raw37521Labels = mixedMoment B raw37521step0 raw37521step0Labels := by
      have ha : raw37521step0 = (fun i j => raw37521 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37521step0 raw37521; decide +kernel
      have hl : raw37521step0Labels = raw37521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37521 raw37521Labels permutation170 permutation4
    mixedMoment B raw37521step0 raw37521step0Labels = mixedMoment B raw37521step1 raw37521step1Labels := by
      have ha : raw37521step1 = -raw37521step0 := by apply Matrix.ext; change ∀ i j, raw37521step1 i j = -(raw37521step0 i j); unfold raw37521step1 raw37521step0; decide +kernel
      have hl : raw37521step1Labels = raw37521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw37522 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw37522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37522 raw37522Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37522 raw37522Labels = mixedMoment B raw37522step0 raw37522step0Labels := by
      have ha : raw37522step0 = (fun i j => raw37522 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37522step0 raw37522; decide +kernel
      have hl : raw37522step0Labels = raw37522Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37522 raw37522Labels permutation194 permutation4
    mixedMoment B raw37522step0 raw37522step0Labels = mixedMoment B raw37522step1 raw37522step1Labels := by
      have ha : raw37522step1 = -raw37522step0 := by apply Matrix.ext; change ∀ i j, raw37522step1 i j = -(raw37522step0 i j); unfold raw37522step1 raw37522step0; decide +kernel
      have hl : raw37522step1Labels = raw37522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw37523 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw37523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37523 raw37523Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37523 raw37523Labels = mixedMoment B raw37523step0 raw37523step0Labels := by
      have ha : raw37523step0 = (fun i j => raw37523 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37523step0 raw37523; decide +kernel
      have hl : raw37523step0Labels = raw37523Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37523 raw37523Labels permutation218 permutation4
    mixedMoment B raw37523step0 raw37523step0Labels = mixedMoment B raw37523step1 raw37523step1Labels := by
      have ha : raw37523step1 = -raw37523step0 := by apply Matrix.ext; change ∀ i j, raw37523step1 i j = -(raw37523step0 i j); unfold raw37523step1 raw37523step0; decide +kernel
      have hl : raw37523step1Labels = raw37523step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw37524 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37524 raw37524Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw37524 raw37524Labels = mixedMoment B raw37524step0 raw37524step0Labels := by
      have ha : raw37524step0 = (fun i j => raw37524 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37524step0 raw37524; decide +kernel
      have hl : raw37524step0Labels = raw37524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37524 raw37524Labels permutation240 permutation4
    mixedMoment B raw37524step0 raw37524step0Labels = mixedMoment B raw37524step1 raw37524step1Labels := by
      have ha : raw37524step1 = -raw37524step0 := by apply Matrix.ext; change ∀ i j, raw37524step1 i j = -(raw37524step0 i j); unfold raw37524step1 raw37524step0; decide +kernel
      have hl : raw37524step1Labels = raw37524step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw37525 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw37525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37525 raw37525Labels = mixedMoment B node1497 node1497Labels := by
  calc
    mixedMoment B raw37525 raw37525Labels = mixedMoment B raw37525step0 raw37525step0Labels := by
      have ha : raw37525step0 = (fun i j => raw37525 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37525step0 raw37525; decide +kernel
      have hl : raw37525step0Labels = raw37525Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37525 raw37525Labels permutation246 permutation4
    mixedMoment B raw37525step0 raw37525step0Labels = mixedMoment B raw37525step1 raw37525step1Labels := by
      have ha : raw37525step1 = -raw37525step0 := by apply Matrix.ext; change ∀ i j, raw37525step1 i j = -(raw37525step0 i j); unfold raw37525step1 raw37525step0; decide +kernel
      have hl : raw37525step1Labels = raw37525step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1497 node1497Labels := by rfl

def raw37526 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37526 raw37526Labels = mixedMoment B node658 node658Labels := by
  calc
    mixedMoment B raw37526 raw37526Labels = mixedMoment B raw37526step0 raw37526step0Labels := by
      have ha : raw37526step0 = (fun i j => raw37526 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37526step0 raw37526; decide +kernel
      have hl : raw37526step0Labels = raw37526Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37526 raw37526Labels permutation243 permutation4
    mixedMoment B raw37526step0 raw37526step0Labels = mixedMoment B raw37526step1 raw37526step1Labels := by
      have ha : raw37526step1 = -raw37526step0 := by apply Matrix.ext; change ∀ i j, raw37526step1 i j = -(raw37526step0 i j); unfold raw37526step1 raw37526step0; decide +kernel
      have hl : raw37526step1Labels = raw37526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node658 node658Labels := by rfl

def raw37527 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37527 raw37527Labels = mixedMoment B node658 node658Labels := by
  calc
    mixedMoment B raw37527 raw37527Labels = mixedMoment B raw37527step0 raw37527step0Labels := by
      have ha : raw37527step0 = (fun i j => raw37527 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37527step0 raw37527; decide +kernel
      have hl : raw37527step0Labels = raw37527Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37527 raw37527Labels permutation241 permutation4
    mixedMoment B raw37527step0 raw37527step0Labels = mixedMoment B raw37527step1 raw37527step1Labels := by
      have ha : raw37527step1 = -raw37527step0 := by apply Matrix.ext; change ∀ i j, raw37527step1 i j = -(raw37527step0 i j); unfold raw37527step1 raw37527step0; decide +kernel
      have hl : raw37527step1Labels = raw37527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node658 node658Labels := by rfl

def raw37528 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37528 raw37528Labels = mixedMoment B node658 node658Labels := by
  calc
    mixedMoment B raw37528 raw37528Labels = mixedMoment B raw37528step0 raw37528step0Labels := by
      have ha : raw37528step0 = (fun i j => raw37528 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37528step0 raw37528; decide +kernel
      have hl : raw37528step0Labels = raw37528Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37528 raw37528Labels permutation240 permutation4
    mixedMoment B raw37528step0 raw37528step0Labels = mixedMoment B raw37528step1 raw37528step1Labels := by
      have ha : raw37528step1 = -raw37528step0 := by apply Matrix.ext; change ∀ i j, raw37528step1 i j = -(raw37528step0 i j); unfold raw37528step1 raw37528step0; decide +kernel
      have hl : raw37528step1Labels = raw37528step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node658 node658Labels := by rfl

def raw37529 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw37529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37529 raw37529Labels = mixedMoment B node666 node666Labels := by
  calc
    mixedMoment B raw37529 raw37529Labels = mixedMoment B raw37529step0 raw37529step0Labels := by
      have ha : raw37529step0 = (fun i j => raw37529 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37529step0 raw37529; decide +kernel
      have hl : raw37529step0Labels = raw37529Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37529 raw37529Labels permutation224 permutation4
    mixedMoment B raw37529step0 raw37529step0Labels = mixedMoment B raw37529step1 raw37529step1Labels := by
      have ha : raw37529step1 = -raw37529step0 := by apply Matrix.ext; change ∀ i j, raw37529step1 i j = -(raw37529step0 i j); unfold raw37529step1 raw37529step0; decide +kernel
      have hl : raw37529step1Labels = raw37529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node666 node666Labels := by rfl

def raw37530 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-3, -1, 4]]
def raw37530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37530 raw37530Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw37530 raw37530Labels = mixedMoment B raw37530step0 raw37530step0Labels := by
      have hz : ∀ j, raw37530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37530step0 = (fun i j => raw37530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37530step0 raw37530; decide +kernel
      have hl : raw37530step0Labels = raw37530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37530 raw37530Labels permutation434 hz
    mixedMoment B raw37530step0 raw37530step0Labels = mixedMoment B raw37530step1 raw37530step1Labels := by
      have hz : ∀ j, raw37530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37530step1 = (fun i j => raw37530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37530step1 raw37530step0; decide +kernel
      have hl : raw37530step1Labels = raw37530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37530step0 raw37530step0Labels permutation80 hz
    mixedMoment B raw37530step1 raw37530step1Labels = mixedMoment B raw37530step2 raw37530step2Labels := by
      have ha : raw37530step2 = (fun i j => raw37530step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37530step2 raw37530step1; decide +kernel
      have hl : raw37530step2Labels = raw37530step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37530step1 raw37530step1Labels permutation31 permutation2
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw37531 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, -1, 1], ![-3, -1, 4]]
def raw37531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw37531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37531 raw37531Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw37531 raw37531Labels = mixedMoment B raw37531step0 raw37531step0Labels := by
      have hz : ∀ j, raw37531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37531step0 = (fun i j => raw37531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37531step0 raw37531; decide +kernel
      have hl : raw37531step0Labels = raw37531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37531 raw37531Labels permutation434 hz
    mixedMoment B raw37531step0 raw37531step0Labels = mixedMoment B raw37531step1 raw37531step1Labels := by
      have hz : ∀ j, raw37531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37531step1 = (fun i j => raw37531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37531step1 raw37531step0; decide +kernel
      have hl : raw37531step1Labels = raw37531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37531step0 raw37531step0Labels permutation80 hz
    mixedMoment B raw37531step1 raw37531step1Labels = mixedMoment B raw37531step2 raw37531step2Labels := by
      have ha : raw37531step2 = (fun i j => raw37531step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37531step2 raw37531step1; decide +kernel
      have hl : raw37531step2Labels = raw37531step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37531step1 raw37531step1Labels permutation30 permutation2
    _ = mixedMoment B node1695 node1695Labels := by rfl

def raw37532 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw37532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37532 raw37532Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw37532 raw37532Labels = mixedMoment B raw37532step0 raw37532step0Labels := by
      have hz : ∀ j, raw37532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37532step0 = (fun i j => raw37532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37532step0 raw37532; decide +kernel
      have hl : raw37532step0Labels = raw37532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37532 raw37532Labels permutation434 hz
    mixedMoment B raw37532step0 raw37532step0Labels = mixedMoment B raw37532step1 raw37532step1Labels := by
      have ha : raw37532step1 = (fun i j => raw37532step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37532step1 raw37532step0; decide +kernel
      have hl : raw37532step1Labels = raw37532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37532step0 raw37532step0Labels permutation151 permutation2
    _ = mixedMoment B node1688 node1688Labels := by rfl

def raw37533 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw37533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37533 raw37533Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw37533 raw37533Labels = mixedMoment B raw37533step0 raw37533step0Labels := by
      have hz : ∀ j, raw37533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37533step0 = (fun i j => raw37533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37533step0 raw37533; decide +kernel
      have hl : raw37533step0Labels = raw37533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37533 raw37533Labels permutation346 hz
    mixedMoment B raw37533step0 raw37533step0Labels = mixedMoment B raw37533step1 raw37533step1Labels := by
      have ha : raw37533step1 = (fun i j => raw37533step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37533step1 raw37533step0; decide +kernel
      have hl : raw37533step1Labels = raw37533step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37533step0 raw37533step0Labels permutation151 permutation2
    _ = mixedMoment B node1688 node1688Labels := by rfl

def raw37534 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, -1, 4]]
def raw37534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, -1, 4]]
def raw37534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -2, 1], ![-3, -1, 4]]
def raw37534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw37534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw37534step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37534 raw37534Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw37534 raw37534Labels = mixedMoment B raw37534step0 raw37534step0Labels := by
      have hz : ∀ j, raw37534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37534step0 = (fun i j => raw37534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37534step0 raw37534; decide +kernel
      have hl : raw37534step0Labels = raw37534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37534 raw37534Labels permutation434 hz
    mixedMoment B raw37534step0 raw37534step0Labels = mixedMoment B raw37534step1 raw37534step1Labels := by
      have hz : ∀ j, raw37534step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37534step1 = (fun i j => raw37534step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37534step1 raw37534step0; decide +kernel
      have hl : raw37534step1Labels = raw37534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37534step0 raw37534step0Labels permutation80 hz
    mixedMoment B raw37534step1 raw37534step1Labels = mixedMoment B raw37534step2 raw37534step2Labels := by
      have ha : raw37534step2 = (fun i j => raw37534step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37534step2 raw37534step1; decide +kernel
      have hl : raw37534step2Labels = raw37534step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37534step1 raw37534step1Labels permutation9 permutation4
    mixedMoment B raw37534step2 raw37534step2Labels = mixedMoment B raw37534step3 raw37534step3Labels := by
      have ha : raw37534step3 = -raw37534step2 := by apply Matrix.ext; change ∀ i j, raw37534step3 i j = -(raw37534step2 i j); unfold raw37534step3 raw37534step2; decide +kernel
      have hl : raw37534step3Labels = raw37534step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1695 node1695Labels := by rfl

def raw37535 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, -1, 1], ![-2, -2, 4]]
def raw37535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw37535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37535step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37535 raw37535Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw37535 raw37535Labels = mixedMoment B raw37535step0 raw37535step0Labels := by
      have hz : ∀ j, raw37535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37535step0 = (fun i j => raw37535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37535step0 raw37535; decide +kernel
      have hl : raw37535step0Labels = raw37535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37535 raw37535Labels permutation434 hz
    mixedMoment B raw37535step0 raw37535step0Labels = mixedMoment B raw37535step1 raw37535step1Labels := by
      have hz : ∀ j, raw37535step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37535step1 = (fun i j => raw37535step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37535step1 raw37535step0; decide +kernel
      have hl : raw37535step1Labels = raw37535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37535step0 raw37535step0Labels permutation80 hz
    mixedMoment B raw37535step1 raw37535step1Labels = mixedMoment B raw37535step2 raw37535step2Labels := by
      have ha : raw37535step2 = (fun i j => raw37535step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37535step2 raw37535step1; decide +kernel
      have hl : raw37535step2Labels = raw37535step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37535step1 raw37535step1Labels permutation8 permutation4
    mixedMoment B raw37535step2 raw37535step2Labels = mixedMoment B raw37535step3 raw37535step3Labels := by
      have ha : raw37535step3 = -raw37535step2 := by apply Matrix.ext; change ∀ i j, raw37535step3 i j = -(raw37535step2 i j); unfold raw37535step3 raw37535step2; decide +kernel
      have hl : raw37535step3Labels = raw37535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw37536 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![-4, 4]]
def raw37536Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37536step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![-1, 1], ![-4, 4]]
def raw37536step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37536step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-4, 4]]
def raw37536step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37536step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw37536step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37536 raw37536Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw37536 raw37536Labels = mixedMoment B raw37536step0 raw37536step0Labels := by
      have hz : ∀ j, raw37536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37536step0 = (fun i j => raw37536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37536step0 raw37536; decide +kernel
      have hl : raw37536step0Labels = raw37536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37536 raw37536Labels permutation434 hz
    mixedMoment B raw37536step0 raw37536step0Labels = mixedMoment B raw37536step1 raw37536step1Labels := by
      have hz : ∀ j, raw37536step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37536step1 = (fun i j => raw37536step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37536step1 raw37536step0; decide +kernel
      have hl : raw37536step1Labels = raw37536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37536step0 raw37536step0Labels permutation80 hz
    mixedMoment B raw37536step1 raw37536step1Labels = mixedMoment B raw37536step2 raw37536step2Labels := by
      have ha : raw37536step2 = (fun i j => raw37536step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37536step2 raw37536step1; decide +kernel
      have hl : raw37536step2Labels = raw37536step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37536step1 raw37536step1Labels permutation31 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw37537 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw37537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37537 raw37537Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw37537 raw37537Labels = mixedMoment B raw37537step0 raw37537step0Labels := by
      have hz : ∀ j, raw37537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37537step0 = (fun i j => raw37537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37537step0 raw37537; decide +kernel
      have hl : raw37537step0Labels = raw37537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37537 raw37537Labels permutation434 hz
    mixedMoment B raw37537step0 raw37537step0Labels = mixedMoment B raw37537step1 raw37537step1Labels := by
      have hz : ∀ j, raw37537step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37537step1 = (fun i j => raw37537step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37537step1 raw37537step0; decide +kernel
      have hl : raw37537step1Labels = raw37537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37537step0 raw37537step0Labels permutation80 hz
    mixedMoment B raw37537step1 raw37537step1Labels = mixedMoment B raw37537step2 raw37537step2Labels := by
      have ha : raw37537step2 = -raw37537step1 := by apply Matrix.ext; change ∀ i j, raw37537step2 i j = -(raw37537step1 i j); unfold raw37537step2 raw37537step1; decide +kernel
      have hl : raw37537step2Labels = raw37537step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw37538 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw37538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37538 raw37538Labels = mixedMoment B node3275 node3275Labels := by
  calc
    mixedMoment B raw37538 raw37538Labels = mixedMoment B raw37538step0 raw37538step0Labels := by
      have hz : ∀ j, raw37538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37538step0 = (fun i j => raw37538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37538step0 raw37538; decide +kernel
      have hl : raw37538step0Labels = raw37538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37538 raw37538Labels permutation434 hz
    mixedMoment B raw37538step0 raw37538step0Labels = mixedMoment B raw37538step1 raw37538step1Labels := by
      have hz : ∀ j, raw37538step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37538step1 = (fun i j => raw37538step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37538step1 raw37538step0; decide +kernel
      have hl : raw37538step1Labels = raw37538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37538step0 raw37538step0Labels permutation80 hz
    mixedMoment B raw37538step1 raw37538step1Labels = mixedMoment B raw37538step2 raw37538step2Labels := by
      have ha : raw37538step2 = (fun i j => raw37538step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37538step2 raw37538step1; decide +kernel
      have hl : raw37538step2Labels = raw37538step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37538step1 raw37538step1Labels permutation31 permutation2
    _ = mixedMoment B node3275 node3275Labels := by rfl

def raw37539 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37539 raw37539Labels = mixedMoment B node3262 node3262Labels := by
  calc
    mixedMoment B raw37539 raw37539Labels = mixedMoment B raw37539step0 raw37539step0Labels := by
      have hz : ∀ j, raw37539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37539step0 = (fun i j => raw37539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37539step0 raw37539; decide +kernel
      have hl : raw37539step0Labels = raw37539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37539 raw37539Labels permutation434 hz
    mixedMoment B raw37539step0 raw37539step0Labels = mixedMoment B raw37539step1 raw37539step1Labels := by
      have ha : raw37539step1 = (fun i j => raw37539step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37539step1 raw37539step0; decide +kernel
      have hl : raw37539step1Labels = raw37539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37539step0 raw37539step0Labels permutation149 permutation2
    _ = mixedMoment B node3262 node3262Labels := by rfl

def raw37540 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37540 raw37540Labels = mixedMoment B node3262 node3262Labels := by
  calc
    mixedMoment B raw37540 raw37540Labels = mixedMoment B raw37540step0 raw37540step0Labels := by
      have hz : ∀ j, raw37540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37540step0 = (fun i j => raw37540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37540step0 raw37540; decide +kernel
      have hl : raw37540step0Labels = raw37540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37540 raw37540Labels permutation346 hz
    mixedMoment B raw37540step0 raw37540step0Labels = mixedMoment B raw37540step1 raw37540step1Labels := by
      have ha : raw37540step1 = (fun i j => raw37540step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37540step1 raw37540step0; decide +kernel
      have hl : raw37540step1Labels = raw37540step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37540step0 raw37540step0Labels permutation149 permutation2
    _ = mixedMoment B node3262 node3262Labels := by rfl

def raw37541 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, -1, 1], ![-2, -2, 4]]
def raw37541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37541step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37541 raw37541Labels = mixedMoment B node3275 node3275Labels := by
  calc
    mixedMoment B raw37541 raw37541Labels = mixedMoment B raw37541step0 raw37541step0Labels := by
      have hz : ∀ j, raw37541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37541step0 = (fun i j => raw37541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37541step0 raw37541; decide +kernel
      have hl : raw37541step0Labels = raw37541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37541 raw37541Labels permutation434 hz
    mixedMoment B raw37541step0 raw37541step0Labels = mixedMoment B raw37541step1 raw37541step1Labels := by
      have hz : ∀ j, raw37541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37541step1 = (fun i j => raw37541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37541step1 raw37541step0; decide +kernel
      have hl : raw37541step1Labels = raw37541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37541step0 raw37541step0Labels permutation80 hz
    mixedMoment B raw37541step1 raw37541step1Labels = mixedMoment B raw37541step2 raw37541step2Labels := by
      have ha : raw37541step2 = (fun i j => raw37541step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37541step2 raw37541step1; decide +kernel
      have hl : raw37541step2Labels = raw37541step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37541step1 raw37541step1Labels permutation31 permutation4
    _ = mixedMoment B node3275 node3275Labels := by rfl

def raw37542 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -3, 4]]
def raw37542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37542 raw37542Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw37542 raw37542Labels = mixedMoment B raw37542step0 raw37542step0Labels := by
      have hz : ∀ j, raw37542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37542step0 = (fun i j => raw37542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37542step0 raw37542; decide +kernel
      have hl : raw37542step0Labels = raw37542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37542 raw37542Labels permutation434 hz
    mixedMoment B raw37542step0 raw37542step0Labels = mixedMoment B raw37542step1 raw37542step1Labels := by
      have hz : ∀ j, raw37542step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37542step1 = (fun i j => raw37542step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37542step1 raw37542step0; decide +kernel
      have hl : raw37542step1Labels = raw37542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37542step0 raw37542step0Labels permutation80 hz
    mixedMoment B raw37542step1 raw37542step1Labels = mixedMoment B raw37542step2 raw37542step2Labels := by
      have ha : raw37542step2 = (fun i j => raw37542step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37542step2 raw37542step1; decide +kernel
      have hl : raw37542step2Labels = raw37542step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37542step1 raw37542step1Labels permutation31 permutation4
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw37543 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -3, 4]]
def raw37543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw37543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37543 raw37543Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw37543 raw37543Labels = mixedMoment B raw37543step0 raw37543step0Labels := by
      have hz : ∀ j, raw37543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37543step0 = (fun i j => raw37543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37543step0 raw37543; decide +kernel
      have hl : raw37543step0Labels = raw37543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37543 raw37543Labels permutation434 hz
    mixedMoment B raw37543step0 raw37543step0Labels = mixedMoment B raw37543step1 raw37543step1Labels := by
      have hz : ∀ j, raw37543step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37543step1 = (fun i j => raw37543step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37543step1 raw37543step0; decide +kernel
      have hl : raw37543step1Labels = raw37543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37543step0 raw37543step0Labels permutation80 hz
    mixedMoment B raw37543step1 raw37543step1Labels = mixedMoment B raw37543step2 raw37543step2Labels := by
      have ha : raw37543step2 = (fun i j => raw37543step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37543step2 raw37543step1; decide +kernel
      have hl : raw37543step2Labels = raw37543step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37543step1 raw37543step1Labels permutation31 permutation4
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw37544 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw37544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw37544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37544 raw37544Labels = mixedMoment B node1555 node1555Labels := by
  calc
    mixedMoment B raw37544 raw37544Labels = mixedMoment B raw37544step0 raw37544step0Labels := by
      have hz : ∀ j, raw37544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37544step0 = (fun i j => raw37544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37544step0 raw37544; decide +kernel
      have hl : raw37544step0Labels = raw37544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37544 raw37544Labels permutation434 hz
    mixedMoment B raw37544step0 raw37544step0Labels = mixedMoment B raw37544step1 raw37544step1Labels := by
      have ha : raw37544step1 = (fun i j => raw37544step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37544step1 raw37544step0; decide +kernel
      have hl : raw37544step1Labels = raw37544step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37544step0 raw37544step0Labels permutation34 permutation4
    mixedMoment B raw37544step1 raw37544step1Labels = mixedMoment B raw37544step2 raw37544step2Labels := by
      have ha : raw37544step2 = -raw37544step1 := by apply Matrix.ext; change ∀ i j, raw37544step2 i j = -(raw37544step1 i j); unfold raw37544step2 raw37544step1; decide +kernel
      have hl : raw37544step2Labels = raw37544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1555 node1555Labels := by rfl

def raw37545 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw37545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw37545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37545 raw37545Labels = mixedMoment B node1555 node1555Labels := by
  calc
    mixedMoment B raw37545 raw37545Labels = mixedMoment B raw37545step0 raw37545step0Labels := by
      have hz : ∀ j, raw37545 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37545step0 = (fun i j => raw37545 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37545step0 raw37545; decide +kernel
      have hl : raw37545step0Labels = raw37545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37545 raw37545Labels permutation346 hz
    mixedMoment B raw37545step0 raw37545step0Labels = mixedMoment B raw37545step1 raw37545step1Labels := by
      have ha : raw37545step1 = (fun i j => raw37545step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37545step1 raw37545step0; decide +kernel
      have hl : raw37545step1Labels = raw37545step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37545step0 raw37545step0Labels permutation34 permutation4
    mixedMoment B raw37545step1 raw37545step1Labels = mixedMoment B raw37545step2 raw37545step2Labels := by
      have ha : raw37545step2 = -raw37545step1 := by apply Matrix.ext; change ∀ i j, raw37545step2 i j = -(raw37545step1 i j); unfold raw37545step2 raw37545step1; decide +kernel
      have hl : raw37545step2Labels = raw37545step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1555 node1555Labels := by rfl

def raw37546 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -3, 4]]
def raw37546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![3, 1, -4]]
def raw37546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37546 raw37546Labels = mixedMoment B node1574 node1574Labels := by
  calc
    mixedMoment B raw37546 raw37546Labels = mixedMoment B raw37546step0 raw37546step0Labels := by
      have hz : ∀ j, raw37546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37546step0 = (fun i j => raw37546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37546step0 raw37546; decide +kernel
      have hl : raw37546step0Labels = raw37546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37546 raw37546Labels permutation434 hz
    mixedMoment B raw37546step0 raw37546step0Labels = mixedMoment B raw37546step1 raw37546step1Labels := by
      have hz : ∀ j, raw37546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37546step1 = (fun i j => raw37546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37546step1 raw37546step0; decide +kernel
      have hl : raw37546step1Labels = raw37546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37546step0 raw37546step0Labels permutation80 hz
    mixedMoment B raw37546step1 raw37546step1Labels = mixedMoment B raw37546step2 raw37546step2Labels := by
      have ha : raw37546step2 = (fun i j => raw37546step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37546step2 raw37546step1; decide +kernel
      have hl : raw37546step2Labels = raw37546step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37546step1 raw37546step1Labels permutation31 permutation4
    _ = mixedMoment B node1574 node1574Labels := by rfl

def raw37547 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![-1, 0, 1], ![0, -4, 4]]
def raw37547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw37547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37547 raw37547Labels = mixedMoment B node770 node770Labels := by
  calc
    mixedMoment B raw37547 raw37547Labels = mixedMoment B raw37547step0 raw37547step0Labels := by
      have hz : ∀ j, raw37547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37547step0 = (fun i j => raw37547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37547step0 raw37547; decide +kernel
      have hl : raw37547step0Labels = raw37547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37547 raw37547Labels permutation434 hz
    mixedMoment B raw37547step0 raw37547step0Labels = mixedMoment B raw37547step1 raw37547step1Labels := by
      have hz : ∀ j, raw37547step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37547step1 = (fun i j => raw37547step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37547step1 raw37547step0; decide +kernel
      have hl : raw37547step1Labels = raw37547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37547step0 raw37547step0Labels permutation80 hz
    mixedMoment B raw37547step1 raw37547step1Labels = mixedMoment B raw37547step2 raw37547step2Labels := by
      have ha : raw37547step2 = (fun i j => raw37547step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37547step2 raw37547step1; decide +kernel
      have hl : raw37547step2Labels = raw37547step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37547step1 raw37547step1Labels permutation31 permutation4
    _ = mixedMoment B node770 node770Labels := by rfl

def raw37548 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![-1, 0, 1], ![0, -4, 4]]
def raw37548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw37548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37548 raw37548Labels = mixedMoment B node774 node774Labels := by
  calc
    mixedMoment B raw37548 raw37548Labels = mixedMoment B raw37548step0 raw37548step0Labels := by
      have hz : ∀ j, raw37548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37548step0 = (fun i j => raw37548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37548step0 raw37548; decide +kernel
      have hl : raw37548step0Labels = raw37548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37548 raw37548Labels permutation434 hz
    mixedMoment B raw37548step0 raw37548step0Labels = mixedMoment B raw37548step1 raw37548step1Labels := by
      have hz : ∀ j, raw37548step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37548step1 = (fun i j => raw37548step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37548step1 raw37548step0; decide +kernel
      have hl : raw37548step1Labels = raw37548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37548step0 raw37548step0Labels permutation80 hz
    mixedMoment B raw37548step1 raw37548step1Labels = mixedMoment B raw37548step2 raw37548step2Labels := by
      have ha : raw37548step2 = (fun i j => raw37548step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37548step2 raw37548step1; decide +kernel
      have hl : raw37548step2Labels = raw37548step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37548step1 raw37548step1Labels permutation31 permutation4
    _ = mixedMoment B node774 node774Labels := by rfl

def raw37549 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37549 raw37549Labels = mixedMoment B node762 node762Labels := by
  calc
    mixedMoment B raw37549 raw37549Labels = mixedMoment B raw37549step0 raw37549step0Labels := by
      have hz : ∀ j, raw37549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37549step0 = (fun i j => raw37549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37549step0 raw37549; decide +kernel
      have hl : raw37549step0Labels = raw37549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37549 raw37549Labels permutation434 hz
    mixedMoment B raw37549step0 raw37549step0Labels = mixedMoment B raw37549step1 raw37549step1Labels := by
      have ha : raw37549step1 = (fun i j => raw37549step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37549step1 raw37549step0; decide +kernel
      have hl : raw37549step1Labels = raw37549step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37549step0 raw37549step0Labels permutation151 permutation4
    _ = mixedMoment B node762 node762Labels := by rfl

def raw37550 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -4, 4]]
def raw37550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37550 raw37550Labels = mixedMoment B node762 node762Labels := by
  calc
    mixedMoment B raw37550 raw37550Labels = mixedMoment B raw37550step0 raw37550step0Labels := by
      have hz : ∀ j, raw37550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37550step0 = (fun i j => raw37550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37550step0 raw37550; decide +kernel
      have hl : raw37550step0Labels = raw37550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37550 raw37550Labels permutation346 hz
    mixedMoment B raw37550step0 raw37550step0Labels = mixedMoment B raw37550step1 raw37550step1Labels := by
      have ha : raw37550step1 = (fun i j => raw37550step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37550step1 raw37550step0; decide +kernel
      have hl : raw37550step1Labels = raw37550step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37550step0 raw37550step0Labels permutation151 permutation4
    _ = mixedMoment B node762 node762Labels := by rfl

def raw37551 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -4, 4]]
def raw37551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -4, 4]]
def raw37551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-2, 1, 1], ![0, -4, 4]]
def raw37551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37551 raw37551Labels = mixedMoment B node842 node842Labels := by
  calc
    mixedMoment B raw37551 raw37551Labels = mixedMoment B raw37551step0 raw37551step0Labels := by
      have hz : ∀ j, raw37551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37551step0 = (fun i j => raw37551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37551step0 raw37551; decide +kernel
      have hl : raw37551step0Labels = raw37551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37551 raw37551Labels permutation434 hz
    mixedMoment B raw37551step0 raw37551step0Labels = mixedMoment B raw37551step1 raw37551step1Labels := by
      have hz : ∀ j, raw37551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37551step1 = (fun i j => raw37551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37551step1 raw37551step0; decide +kernel
      have hl : raw37551step1Labels = raw37551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37551step0 raw37551step0Labels permutation80 hz
    mixedMoment B raw37551step1 raw37551step1Labels = mixedMoment B raw37551step2 raw37551step2Labels := by
      have ha : raw37551step2 = (fun i j => raw37551step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37551step2 raw37551step1; decide +kernel
      have hl : raw37551step2Labels = raw37551step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37551step1 raw37551step1Labels permutation31 permutation4
    _ = mixedMoment B node842 node842Labels := by rfl

def raw37552 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw37552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw37552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37552 raw37552Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw37552 raw37552Labels = mixedMoment B raw37552step0 raw37552step0Labels := by
      have hz : ∀ j, raw37552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37552step0 = (fun i j => raw37552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37552step0 raw37552; decide +kernel
      have hl : raw37552step0Labels = raw37552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37552 raw37552Labels permutation434 hz
    mixedMoment B raw37552step0 raw37552step0Labels = mixedMoment B raw37552step1 raw37552step1Labels := by
      have hz : ∀ j, raw37552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37552step1 = (fun i j => raw37552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37552step1 raw37552step0; decide +kernel
      have hl : raw37552step1Labels = raw37552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37552step0 raw37552step0Labels permutation80 hz
    mixedMoment B raw37552step1 raw37552step1Labels = mixedMoment B raw37552step2 raw37552step2Labels := by
      have ha : raw37552step2 = (fun i j => raw37552step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37552step2 raw37552step1; decide +kernel
      have hl : raw37552step2Labels = raw37552step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37552step1 raw37552step1Labels permutation31 permutation2
    _ = mixedMoment B node2167 node2167Labels := by rfl

def raw37553 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw37553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-2, 0, 2]]
def raw37553step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw37553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37553 raw37553Labels = mixedMoment B node1743 node1743Labels := by
  calc
    mixedMoment B raw37553 raw37553Labels = mixedMoment B raw37553step0 raw37553step0Labels := by
      have hz : ∀ j, raw37553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37553step0 = (fun i j => raw37553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37553step0 raw37553; decide +kernel
      have hl : raw37553step0Labels = raw37553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37553 raw37553Labels permutation434 hz
    mixedMoment B raw37553step0 raw37553step0Labels = mixedMoment B raw37553step1 raw37553step1Labels := by
      have hz : ∀ j, raw37553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37553step1 = (fun i j => raw37553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37553step1 raw37553step0; decide +kernel
      have hl : raw37553step1Labels = raw37553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37553step0 raw37553step0Labels permutation80 hz
    mixedMoment B raw37553step1 raw37553step1Labels = mixedMoment B raw37553step2 raw37553step2Labels := by
      have ha : raw37553step2 = (fun i j => raw37553step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37553step2 raw37553step1; decide +kernel
      have hl : raw37553step2Labels = raw37553step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37553step1 raw37553step1Labels permutation12 permutation4
    mixedMoment B raw37553step2 raw37553step2Labels = mixedMoment B raw37553step3 raw37553step3Labels := by
      have ha : raw37553step3 = -raw37553step2 := by apply Matrix.ext; change ∀ i j, raw37553step3 i j = -(raw37553step2 i j); unfold raw37553step3 raw37553step2; decide +kernel
      have hl : raw37553step3Labels = raw37553step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1743 node1743Labels := by rfl

def raw37554 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw37554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37554 raw37554Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw37554 raw37554Labels = mixedMoment B raw37554step0 raw37554step0Labels := by
      have hz : ∀ j, raw37554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37554step0 = (fun i j => raw37554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37554step0 raw37554; decide +kernel
      have hl : raw37554step0Labels = raw37554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37554 raw37554Labels permutation434 hz
    mixedMoment B raw37554step0 raw37554step0Labels = mixedMoment B raw37554step1 raw37554step1Labels := by
      have ha : raw37554step1 = (fun i j => raw37554step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37554step1 raw37554step0; decide +kernel
      have hl : raw37554step1Labels = raw37554step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37554step0 raw37554step0Labels permutation36 permutation4
    mixedMoment B raw37554step1 raw37554step1Labels = mixedMoment B raw37554step2 raw37554step2Labels := by
      have ha : raw37554step2 = -raw37554step1 := by apply Matrix.ext; change ∀ i j, raw37554step2 i j = -(raw37554step1 i j); unfold raw37554step2 raw37554step1; decide +kernel
      have hl : raw37554step2Labels = raw37554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1685 node1685Labels := by rfl

def raw37555 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw37555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37555 raw37555Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw37555 raw37555Labels = mixedMoment B raw37555step0 raw37555step0Labels := by
      have hz : ∀ j, raw37555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37555step0 = (fun i j => raw37555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37555step0 raw37555; decide +kernel
      have hl : raw37555step0Labels = raw37555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37555 raw37555Labels permutation346 hz
    mixedMoment B raw37555step0 raw37555step0Labels = mixedMoment B raw37555step1 raw37555step1Labels := by
      have ha : raw37555step1 = (fun i j => raw37555step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37555step1 raw37555step0; decide +kernel
      have hl : raw37555step1Labels = raw37555step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37555step0 raw37555step0Labels permutation36 permutation4
    mixedMoment B raw37555step1 raw37555step1Labels = mixedMoment B raw37555step2 raw37555step2Labels := by
      have ha : raw37555step2 = -raw37555step1 := by apply Matrix.ext; change ∀ i j, raw37555step2 i j = -(raw37555step1 i j); unfold raw37555step2 raw37555step1; decide +kernel
      have hl : raw37555step2Labels = raw37555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1685 node1685Labels := by rfl

def raw37556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -3, 2], ![-3, 0, 3]]
def raw37556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw37556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37556step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw37556step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37556 raw37556Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw37556 raw37556Labels = mixedMoment B raw37556step0 raw37556step0Labels := by
      have hz : ∀ j, raw37556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37556step0 = (fun i j => raw37556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37556step0 raw37556; decide +kernel
      have hl : raw37556step0Labels = raw37556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37556 raw37556Labels permutation434 hz
    mixedMoment B raw37556step0 raw37556step0Labels = mixedMoment B raw37556step1 raw37556step1Labels := by
      have hz : ∀ j, raw37556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37556step1 = (fun i j => raw37556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37556step1 raw37556step0; decide +kernel
      have hl : raw37556step1Labels = raw37556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37556step0 raw37556step0Labels permutation80 hz
    mixedMoment B raw37556step1 raw37556step1Labels = mixedMoment B raw37556step2 raw37556step2Labels := by
      have ha : raw37556step2 = (fun i j => raw37556step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37556step2 raw37556step1; decide +kernel
      have hl : raw37556step2Labels = raw37556step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37556step1 raw37556step1Labels permutation9 permutation4
    mixedMoment B raw37556step2 raw37556step2Labels = mixedMoment B raw37556step3 raw37556step3Labels := by
      have ha : raw37556step3 = -raw37556step2 := by apply Matrix.ext; change ∀ i j, raw37556step3 i j = -(raw37556step2 i j); unfold raw37556step3 raw37556step2; decide +kernel
      have hl : raw37556step3Labels = raw37556step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1687 node1687Labels := by rfl

def raw37557 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, -2, 2], ![-2, -1, 3]]
def raw37557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw37557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37557step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37557step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37557 raw37557Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw37557 raw37557Labels = mixedMoment B raw37557step0 raw37557step0Labels := by
      have hz : ∀ j, raw37557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37557step0 = (fun i j => raw37557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37557step0 raw37557; decide +kernel
      have hl : raw37557step0Labels = raw37557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37557 raw37557Labels permutation434 hz
    mixedMoment B raw37557step0 raw37557step0Labels = mixedMoment B raw37557step1 raw37557step1Labels := by
      have hz : ∀ j, raw37557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37557step1 = (fun i j => raw37557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37557step1 raw37557step0; decide +kernel
      have hl : raw37557step1Labels = raw37557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37557step0 raw37557step0Labels permutation80 hz
    mixedMoment B raw37557step1 raw37557step1Labels = mixedMoment B raw37557step2 raw37557step2Labels := by
      have ha : raw37557step2 = (fun i j => raw37557step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37557step2 raw37557step1; decide +kernel
      have hl : raw37557step2Labels = raw37557step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37557step1 raw37557step1Labels permutation9 permutation4
    mixedMoment B raw37557step2 raw37557step2Labels = mixedMoment B raw37557step3 raw37557step3Labels := by
      have ha : raw37557step3 = -raw37557step2 := by apply Matrix.ext; change ∀ i j, raw37557step3 i j = -(raw37557step2 i j); unfold raw37557step3 raw37557step2; decide +kernel
      have hl : raw37557step3Labels = raw37557step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1694 node1694Labels := by rfl

def raw37558 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37558Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37558step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37558step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37558step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-2, 2], ![-3, 3]]
def raw37558step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37558step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw37558step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37558 raw37558Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw37558 raw37558Labels = mixedMoment B raw37558step0 raw37558step0Labels := by
      have hz : ∀ j, raw37558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37558step0 = (fun i j => raw37558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37558step0 raw37558; decide +kernel
      have hl : raw37558step0Labels = raw37558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37558 raw37558Labels permutation434 hz
    mixedMoment B raw37558step0 raw37558step0Labels = mixedMoment B raw37558step1 raw37558step1Labels := by
      have hz : ∀ j, raw37558step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37558step1 = (fun i j => raw37558step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37558step1 raw37558step0; decide +kernel
      have hl : raw37558step1Labels = raw37558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37558step0 raw37558step0Labels permutation80 hz
    mixedMoment B raw37558step1 raw37558step1Labels = mixedMoment B raw37558step2 raw37558step2Labels := by
      have ha : raw37558step2 = -raw37558step1 := by apply Matrix.ext; change ∀ i j, raw37558step2 i j = -(raw37558step1 i j); unfold raw37558step2 raw37558step1; decide +kernel
      have hl : raw37558step2Labels = raw37558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4067 node4067Labels := by rfl

def raw37559 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-2, 0, 2], ![-1, -2, 3]]
def raw37559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw37559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37559step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37559step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37559 raw37559Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw37559 raw37559Labels = mixedMoment B raw37559step0 raw37559step0Labels := by
      have hz : ∀ j, raw37559 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37559step0 = (fun i j => raw37559 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37559step0 raw37559; decide +kernel
      have hl : raw37559step0Labels = raw37559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37559 raw37559Labels permutation434 hz
    mixedMoment B raw37559step0 raw37559step0Labels = mixedMoment B raw37559step1 raw37559step1Labels := by
      have hz : ∀ j, raw37559step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37559step1 = (fun i j => raw37559step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37559step1 raw37559step0; decide +kernel
      have hl : raw37559step1Labels = raw37559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37559step0 raw37559step0Labels permutation80 hz
    mixedMoment B raw37559step1 raw37559step1Labels = mixedMoment B raw37559step2 raw37559step2Labels := by
      have ha : raw37559step2 = (fun i j => raw37559step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37559step2 raw37559step1; decide +kernel
      have hl : raw37559step2Labels = raw37559step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37559step1 raw37559step1Labels permutation9 permutation2
    mixedMoment B raw37559step2 raw37559step2Labels = mixedMoment B raw37559step3 raw37559step3Labels := by
      have ha : raw37559step3 = -raw37559step2 := by apply Matrix.ext; change ∀ i j, raw37559step3 i j = -(raw37559step2 i j); unfold raw37559step3 raw37559step2; decide +kernel
      have hl : raw37559step3Labels = raw37559step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3277 node3277Labels := by rfl

def raw37560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![-2, 0, 2], ![-1, -2, 3]]
def raw37560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw37560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37560step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw37560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37560 raw37560Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw37560 raw37560Labels = mixedMoment B raw37560step0 raw37560step0Labels := by
      have hz : ∀ j, raw37560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37560step0 = (fun i j => raw37560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37560step0 raw37560; decide +kernel
      have hl : raw37560step0Labels = raw37560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37560 raw37560Labels permutation434 hz
    mixedMoment B raw37560step0 raw37560step0Labels = mixedMoment B raw37560step1 raw37560step1Labels := by
      have hz : ∀ j, raw37560step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37560step1 = (fun i j => raw37560step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37560step1 raw37560step0; decide +kernel
      have hl : raw37560step1Labels = raw37560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37560step0 raw37560step0Labels permutation80 hz
    mixedMoment B raw37560step1 raw37560step1Labels = mixedMoment B raw37560step2 raw37560step2Labels := by
      have ha : raw37560step2 = (fun i j => raw37560step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37560step2 raw37560step1; decide +kernel
      have hl : raw37560step2Labels = raw37560step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37560step1 raw37560step1Labels permutation10 permutation4
    mixedMoment B raw37560step2 raw37560step2Labels = mixedMoment B raw37560step3 raw37560step3Labels := by
      have ha : raw37560step3 = -raw37560step2 := by apply Matrix.ext; change ∀ i j, raw37560step3 i j = -(raw37560step2 i j); unfold raw37560step3 raw37560step2; decide +kernel
      have hl : raw37560step3Labels = raw37560step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1735 node1735Labels := by rfl

def raw37561 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37561step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37561 raw37561Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw37561 raw37561Labels = mixedMoment B raw37561step0 raw37561step0Labels := by
      have hz : ∀ j, raw37561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37561step0 = (fun i j => raw37561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37561step0 raw37561; decide +kernel
      have hl : raw37561step0Labels = raw37561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37561 raw37561Labels permutation434 hz
    mixedMoment B raw37561step0 raw37561step0Labels = mixedMoment B raw37561step1 raw37561step1Labels := by
      have ha : raw37561step1 = (fun i j => raw37561step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37561step1 raw37561step0; decide +kernel
      have hl : raw37561step1Labels = raw37561step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37561step0 raw37561step0Labels permutation34 permutation4
    mixedMoment B raw37561step1 raw37561step1Labels = mixedMoment B raw37561step2 raw37561step2Labels := by
      have ha : raw37561step2 = -raw37561step1 := by apply Matrix.ext; change ∀ i j, raw37561step2 i j = -(raw37561step1 i j); unfold raw37561step2 raw37561step1; decide +kernel
      have hl : raw37561step2Labels = raw37561step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw37562 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37562 raw37562Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw37562 raw37562Labels = mixedMoment B raw37562step0 raw37562step0Labels := by
      have hz : ∀ j, raw37562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37562step0 = (fun i j => raw37562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37562step0 raw37562; decide +kernel
      have hl : raw37562step0Labels = raw37562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37562 raw37562Labels permutation346 hz
    mixedMoment B raw37562step0 raw37562step0Labels = mixedMoment B raw37562step1 raw37562step1Labels := by
      have ha : raw37562step1 = (fun i j => raw37562step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37562step1 raw37562step0; decide +kernel
      have hl : raw37562step1Labels = raw37562step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37562step0 raw37562step0Labels permutation34 permutation4
    mixedMoment B raw37562step1 raw37562step1Labels = mixedMoment B raw37562step2 raw37562step2Labels := by
      have ha : raw37562step2 = -raw37562step1 := by apply Matrix.ext; change ∀ i j, raw37562step2 i j = -(raw37562step1 i j); unfold raw37562step2 raw37562step1; decide +kernel
      have hl : raw37562step2Labels = raw37562step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw37563 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw37563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37563step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37563step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37563 raw37563Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw37563 raw37563Labels = mixedMoment B raw37563step0 raw37563step0Labels := by
      have hz : ∀ j, raw37563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37563step0 = (fun i j => raw37563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37563step0 raw37563; decide +kernel
      have hl : raw37563step0Labels = raw37563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37563 raw37563Labels permutation434 hz
    mixedMoment B raw37563step0 raw37563step0Labels = mixedMoment B raw37563step1 raw37563step1Labels := by
      have hz : ∀ j, raw37563step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37563step1 = (fun i j => raw37563step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37563step1 raw37563step0; decide +kernel
      have hl : raw37563step1Labels = raw37563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37563step0 raw37563step0Labels permutation80 hz
    mixedMoment B raw37563step1 raw37563step1Labels = mixedMoment B raw37563step2 raw37563step2Labels := by
      have ha : raw37563step2 = (fun i j => raw37563step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37563step2 raw37563step1; decide +kernel
      have hl : raw37563step2Labels = raw37563step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37563step1 raw37563step1Labels permutation8 permutation4
    mixedMoment B raw37563step2 raw37563step2Labels = mixedMoment B raw37563step3 raw37563step3Labels := by
      have ha : raw37563step3 = -raw37563step2 := by apply Matrix.ext; change ∀ i j, raw37563step3 i j = -(raw37563step2 i j); unfold raw37563step3 raw37563step2; decide +kernel
      have hl : raw37563step3Labels = raw37563step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw37564 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-2, 0, 2], ![0, -3, 3]]
def raw37564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw37564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37564step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw37564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37564 raw37564Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw37564 raw37564Labels = mixedMoment B raw37564step0 raw37564step0Labels := by
      have hz : ∀ j, raw37564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37564step0 = (fun i j => raw37564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37564step0 raw37564; decide +kernel
      have hl : raw37564step0Labels = raw37564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37564 raw37564Labels permutation434 hz
    mixedMoment B raw37564step0 raw37564step0Labels = mixedMoment B raw37564step1 raw37564step1Labels := by
      have hz : ∀ j, raw37564step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37564step1 = (fun i j => raw37564step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37564step1 raw37564step0; decide +kernel
      have hl : raw37564step1Labels = raw37564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37564step0 raw37564step0Labels permutation80 hz
    mixedMoment B raw37564step1 raw37564step1Labels = mixedMoment B raw37564step2 raw37564step2Labels := by
      have ha : raw37564step2 = (fun i j => raw37564step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37564step2 raw37564step1; decide +kernel
      have hl : raw37564step2Labels = raw37564step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37564step1 raw37564step1Labels permutation8 permutation4
    mixedMoment B raw37564step2 raw37564step2Labels = mixedMoment B raw37564step3 raw37564step3Labels := by
      have ha : raw37564step3 = -raw37564step2 := by apply Matrix.ext; change ∀ i j, raw37564step3 i j = -(raw37564step2 i j); unfold raw37564step3 raw37564step2; decide +kernel
      have hl : raw37564step3Labels = raw37564step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw37565 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37565 raw37565Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw37565 raw37565Labels = mixedMoment B raw37565step0 raw37565step0Labels := by
      have hz : ∀ j, raw37565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37565step0 = (fun i j => raw37565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37565step0 raw37565; decide +kernel
      have hl : raw37565step0Labels = raw37565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37565 raw37565Labels permutation434 hz
    mixedMoment B raw37565step0 raw37565step0Labels = mixedMoment B raw37565step1 raw37565step1Labels := by
      have hz : ∀ j, raw37565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37565step1 = (fun i j => raw37565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37565step1 raw37565step0; decide +kernel
      have hl : raw37565step1Labels = raw37565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37565step0 raw37565step0Labels permutation80 hz
    mixedMoment B raw37565step1 raw37565step1Labels = mixedMoment B raw37565step2 raw37565step2Labels := by
      have ha : raw37565step2 = -raw37565step1 := by apply Matrix.ext; change ∀ i j, raw37565step2 i j = -(raw37565step1 i j); unfold raw37565step2 raw37565step1; decide +kernel
      have hl : raw37565step2Labels = raw37565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3276 node3276Labels := by rfl

def raw37566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw37566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw37566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37566 raw37566Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw37566 raw37566Labels = mixedMoment B raw37566step0 raw37566step0Labels := by
      have hz : ∀ j, raw37566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37566step0 = (fun i j => raw37566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37566step0 raw37566; decide +kernel
      have hl : raw37566step0Labels = raw37566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37566 raw37566Labels permutation434 hz
    mixedMoment B raw37566step0 raw37566step0Labels = mixedMoment B raw37566step1 raw37566step1Labels := by
      have hz : ∀ j, raw37566step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37566step1 = (fun i j => raw37566step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37566step1 raw37566step0; decide +kernel
      have hl : raw37566step1Labels = raw37566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37566step0 raw37566step0Labels permutation80 hz
    mixedMoment B raw37566step1 raw37566step1Labels = mixedMoment B raw37566step2 raw37566step2Labels := by
      have ha : raw37566step2 = (fun i j => raw37566step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37566step2 raw37566step1; decide +kernel
      have hl : raw37566step2Labels = raw37566step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37566step1 raw37566step1Labels permutation8 permutation4
    mixedMoment B raw37566step2 raw37566step2Labels = mixedMoment B raw37566step3 raw37566step3Labels := by
      have ha : raw37566step3 = -raw37566step2 := by apply Matrix.ext; change ∀ i j, raw37566step3 i j = -(raw37566step2 i j); unfold raw37566step3 raw37566step2; decide +kernel
      have hl : raw37566step3Labels = raw37566step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1748 node1748Labels := by rfl

def raw37567 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37567 raw37567Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw37567 raw37567Labels = mixedMoment B raw37567step0 raw37567step0Labels := by
      have hz : ∀ j, raw37567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37567step0 = (fun i j => raw37567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37567step0 raw37567; decide +kernel
      have hl : raw37567step0Labels = raw37567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37567 raw37567Labels permutation434 hz
    mixedMoment B raw37567step0 raw37567step0Labels = mixedMoment B raw37567step1 raw37567step1Labels := by
      have ha : raw37567step1 = (fun i j => raw37567step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37567step1 raw37567step0; decide +kernel
      have hl : raw37567step1Labels = raw37567step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37567step0 raw37567step0Labels permutation32 permutation4
    mixedMoment B raw37567step1 raw37567step1Labels = mixedMoment B raw37567step2 raw37567step2Labels := by
      have ha : raw37567step2 = -raw37567step1 := by apply Matrix.ext; change ∀ i j, raw37567step2 i j = -(raw37567step1 i j); unfold raw37567step2 raw37567step1; decide +kernel
      have hl : raw37567step2Labels = raw37567step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw37568 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37568 raw37568Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw37568 raw37568Labels = mixedMoment B raw37568step0 raw37568step0Labels := by
      have hz : ∀ j, raw37568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37568step0 = (fun i j => raw37568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37568step0 raw37568; decide +kernel
      have hl : raw37568step0Labels = raw37568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37568 raw37568Labels permutation346 hz
    mixedMoment B raw37568step0 raw37568step0Labels = mixedMoment B raw37568step1 raw37568step1Labels := by
      have ha : raw37568step1 = (fun i j => raw37568step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37568step1 raw37568step0; decide +kernel
      have hl : raw37568step1Labels = raw37568step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37568step0 raw37568step0Labels permutation32 permutation4
    mixedMoment B raw37568step1 raw37568step1Labels = mixedMoment B raw37568step2 raw37568step2Labels := by
      have ha : raw37568step2 = -raw37568step1 := by apply Matrix.ext; change ∀ i j, raw37568step2 i j = -(raw37568step1 i j); unfold raw37568step2 raw37568step1; decide +kernel
      have hl : raw37568step2Labels = raw37568step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw37569 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw37569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw37569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37569 raw37569Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw37569 raw37569Labels = mixedMoment B raw37569step0 raw37569step0Labels := by
      have hz : ∀ j, raw37569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37569step0 = (fun i j => raw37569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37569step0 raw37569; decide +kernel
      have hl : raw37569step0Labels = raw37569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37569 raw37569Labels permutation434 hz
    mixedMoment B raw37569step0 raw37569step0Labels = mixedMoment B raw37569step1 raw37569step1Labels := by
      have hz : ∀ j, raw37569step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37569step1 = (fun i j => raw37569step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37569step1 raw37569step0; decide +kernel
      have hl : raw37569step1Labels = raw37569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37569step0 raw37569step0Labels permutation80 hz
    mixedMoment B raw37569step1 raw37569step1Labels = mixedMoment B raw37569step2 raw37569step2Labels := by
      have ha : raw37569step2 = -raw37569step1 := by apply Matrix.ext; change ∀ i j, raw37569step2 i j = -(raw37569step1 i j); unfold raw37569step2 raw37569step1; decide +kernel
      have hl : raw37569step2Labels = raw37569step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw37570 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37570 raw37570Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw37570 raw37570Labels = mixedMoment B raw37570step0 raw37570step0Labels := by
      have hz : ∀ j, raw37570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37570step0 = (fun i j => raw37570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37570step0 raw37570; decide +kernel
      have hl : raw37570step0Labels = raw37570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37570 raw37570Labels permutation434 hz
    mixedMoment B raw37570step0 raw37570step0Labels = mixedMoment B raw37570step1 raw37570step1Labels := by
      have ha : raw37570step1 = (fun i j => raw37570step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37570step1 raw37570step0; decide +kernel
      have hl : raw37570step1Labels = raw37570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37570step0 raw37570step0Labels permutation149 permutation2
    _ = mixedMoment B node2149 node2149Labels := by rfl

def raw37571 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37571 raw37571Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw37571 raw37571Labels = mixedMoment B raw37571step0 raw37571step0Labels := by
      have hz : ∀ j, raw37571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37571step0 = (fun i j => raw37571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37571step0 raw37571; decide +kernel
      have hl : raw37571step0Labels = raw37571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37571 raw37571Labels permutation346 hz
    mixedMoment B raw37571step0 raw37571step0Labels = mixedMoment B raw37571step1 raw37571step1Labels := by
      have ha : raw37571step1 = (fun i j => raw37571step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37571step1 raw37571step0; decide +kernel
      have hl : raw37571step1Labels = raw37571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37571step0 raw37571step0Labels permutation149 permutation2
    _ = mixedMoment B node2149 node2149Labels := by rfl

def raw37572 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -3, 2], ![-3, 0, 3]]
def raw37572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw37572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37572 raw37572Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw37572 raw37572Labels = mixedMoment B raw37572step0 raw37572step0Labels := by
      have hz : ∀ j, raw37572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37572step0 = (fun i j => raw37572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37572step0 raw37572; decide +kernel
      have hl : raw37572step0Labels = raw37572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37572 raw37572Labels permutation434 hz
    mixedMoment B raw37572step0 raw37572step0Labels = mixedMoment B raw37572step1 raw37572step1Labels := by
      have hz : ∀ j, raw37572step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37572step1 = (fun i j => raw37572step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37572step1 raw37572step0; decide +kernel
      have hl : raw37572step1Labels = raw37572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37572step0 raw37572step0Labels permutation80 hz
    mixedMoment B raw37572step1 raw37572step1Labels = mixedMoment B raw37572step2 raw37572step2Labels := by
      have ha : raw37572step2 = (fun i j => raw37572step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37572step2 raw37572step1; decide +kernel
      have hl : raw37572step2Labels = raw37572step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37572step1 raw37572step1Labels permutation29 permutation2
    _ = mixedMoment B node2258 node2258Labels := by rfl

def raw37573 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, -2, 2], ![-2, -1, 3]]
def raw37573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw37573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37573step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37573 raw37573Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw37573 raw37573Labels = mixedMoment B raw37573step0 raw37573step0Labels := by
      have hz : ∀ j, raw37573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37573step0 = (fun i j => raw37573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37573step0 raw37573; decide +kernel
      have hl : raw37573step0Labels = raw37573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37573 raw37573Labels permutation434 hz
    mixedMoment B raw37573step0 raw37573step0Labels = mixedMoment B raw37573step1 raw37573step1Labels := by
      have hz : ∀ j, raw37573step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37573step1 = (fun i j => raw37573step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37573step1 raw37573step0; decide +kernel
      have hl : raw37573step1Labels = raw37573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37573step0 raw37573step0Labels permutation80 hz
    mixedMoment B raw37573step1 raw37573step1Labels = mixedMoment B raw37573step2 raw37573step2Labels := by
      have ha : raw37573step2 = (fun i j => raw37573step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37573step2 raw37573step1; decide +kernel
      have hl : raw37573step2Labels = raw37573step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37573step1 raw37573step1Labels permutation9 permutation4
    mixedMoment B raw37573step2 raw37573step2Labels = mixedMoment B raw37573step3 raw37573step3Labels := by
      have ha : raw37573step3 = -raw37573step2 := by apply Matrix.ext; change ∀ i j, raw37573step3 i j = -(raw37573step2 i j); unfold raw37573step3 raw37573step2; decide +kernel
      have hl : raw37573step3Labels = raw37573step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3277 node3277Labels := by rfl

def raw37574 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-2, 0, 2], ![-1, -2, 3]]
def raw37574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw37574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37574step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37574step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37574 raw37574Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw37574 raw37574Labels = mixedMoment B raw37574step0 raw37574step0Labels := by
      have hz : ∀ j, raw37574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37574step0 = (fun i j => raw37574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37574step0 raw37574; decide +kernel
      have hl : raw37574step0Labels = raw37574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37574 raw37574Labels permutation434 hz
    mixedMoment B raw37574step0 raw37574step0Labels = mixedMoment B raw37574step1 raw37574step1Labels := by
      have hz : ∀ j, raw37574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37574step1 = (fun i j => raw37574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37574step1 raw37574step0; decide +kernel
      have hl : raw37574step1Labels = raw37574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37574step0 raw37574step0Labels permutation80 hz
    mixedMoment B raw37574step1 raw37574step1Labels = mixedMoment B raw37574step2 raw37574step2Labels := by
      have ha : raw37574step2 = (fun i j => raw37574step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37574step2 raw37574step1; decide +kernel
      have hl : raw37574step2Labels = raw37574step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37574step1 raw37574step1Labels permutation9 permutation2
    mixedMoment B raw37574step2 raw37574step2Labels = mixedMoment B raw37574step3 raw37574step3Labels := by
      have ha : raw37574step3 = -raw37574step2 := by apply Matrix.ext; change ∀ i j, raw37574step3 i j = -(raw37574step2 i j); unfold raw37574step3 raw37574step2; decide +kernel
      have hl : raw37574step3Labels = raw37574step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1694 node1694Labels := by rfl

def raw37575 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37575 raw37575Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw37575 raw37575Labels = mixedMoment B raw37575step0 raw37575step0Labels := by
      have hz : ∀ j, raw37575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37575step0 = (fun i j => raw37575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37575step0 raw37575; decide +kernel
      have hl : raw37575step0Labels = raw37575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37575 raw37575Labels permutation434 hz
    mixedMoment B raw37575step0 raw37575step0Labels = mixedMoment B raw37575step1 raw37575step1Labels := by
      have ha : raw37575step1 = (fun i j => raw37575step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37575step1 raw37575step0; decide +kernel
      have hl : raw37575step1Labels = raw37575step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37575step0 raw37575step0Labels permutation34 permutation4
    mixedMoment B raw37575step1 raw37575step1Labels = mixedMoment B raw37575step2 raw37575step2Labels := by
      have ha : raw37575step2 = -raw37575step1 := by apply Matrix.ext; change ∀ i j, raw37575step2 i j = -(raw37575step1 i j); unfold raw37575step2 raw37575step1; decide +kernel
      have hl : raw37575step2Labels = raw37575step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3268 node3268Labels := by rfl

def raw37576 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37576 raw37576Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw37576 raw37576Labels = mixedMoment B raw37576step0 raw37576step0Labels := by
      have hz : ∀ j, raw37576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37576step0 = (fun i j => raw37576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37576step0 raw37576; decide +kernel
      have hl : raw37576step0Labels = raw37576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37576 raw37576Labels permutation346 hz
    mixedMoment B raw37576step0 raw37576step0Labels = mixedMoment B raw37576step1 raw37576step1Labels := by
      have ha : raw37576step1 = (fun i j => raw37576step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37576step1 raw37576step0; decide +kernel
      have hl : raw37576step1Labels = raw37576step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37576step0 raw37576step0Labels permutation34 permutation4
    mixedMoment B raw37576step1 raw37576step1Labels = mixedMoment B raw37576step2 raw37576step2Labels := by
      have ha : raw37576step2 = -raw37576step1 := by apply Matrix.ext; change ∀ i j, raw37576step2 i j = -(raw37576step1 i j); unfold raw37576step2 raw37576step1; decide +kernel
      have hl : raw37576step2Labels = raw37576step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3268 node3268Labels := by rfl

def raw37577 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw37577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37577step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37577 raw37577Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw37577 raw37577Labels = mixedMoment B raw37577step0 raw37577step0Labels := by
      have hz : ∀ j, raw37577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37577step0 = (fun i j => raw37577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37577step0 raw37577; decide +kernel
      have hl : raw37577step0Labels = raw37577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37577 raw37577Labels permutation434 hz
    mixedMoment B raw37577step0 raw37577step0Labels = mixedMoment B raw37577step1 raw37577step1Labels := by
      have hz : ∀ j, raw37577step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37577step1 = (fun i j => raw37577step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37577step1 raw37577step0; decide +kernel
      have hl : raw37577step1Labels = raw37577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37577step0 raw37577step0Labels permutation80 hz
    mixedMoment B raw37577step1 raw37577step1Labels = mixedMoment B raw37577step2 raw37577step2Labels := by
      have ha : raw37577step2 = (fun i j => raw37577step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37577step2 raw37577step1; decide +kernel
      have hl : raw37577step2Labels = raw37577step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37577step1 raw37577step1Labels permutation8 permutation4
    mixedMoment B raw37577step2 raw37577step2Labels = mixedMoment B raw37577step3 raw37577step3Labels := by
      have ha : raw37577step3 = -raw37577step2 := by apply Matrix.ext; change ∀ i j, raw37577step3 i j = -(raw37577step2 i j); unfold raw37577step3 raw37577step2; decide +kernel
      have hl : raw37577step3Labels = raw37577step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3276 node3276Labels := by rfl

def raw37578 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-2, 0, 2], ![0, -3, 3]]
def raw37578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw37578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37578 raw37578Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw37578 raw37578Labels = mixedMoment B raw37578step0 raw37578step0Labels := by
      have hz : ∀ j, raw37578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37578step0 = (fun i j => raw37578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37578step0 raw37578; decide +kernel
      have hl : raw37578step0Labels = raw37578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37578 raw37578Labels permutation434 hz
    mixedMoment B raw37578step0 raw37578step0Labels = mixedMoment B raw37578step1 raw37578step1Labels := by
      have hz : ∀ j, raw37578step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37578step1 = (fun i j => raw37578step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37578step1 raw37578step0; decide +kernel
      have hl : raw37578step1Labels = raw37578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37578step0 raw37578step0Labels permutation80 hz
    mixedMoment B raw37578step1 raw37578step1Labels = mixedMoment B raw37578step2 raw37578step2Labels := by
      have ha : raw37578step2 = (fun i j => raw37578step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37578step2 raw37578step1; decide +kernel
      have hl : raw37578step2Labels = raw37578step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37578step1 raw37578step1Labels permutation31 permutation4
    _ = mixedMoment B node2167 node2167Labels := by rfl

def raw37579 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37579 raw37579Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw37579 raw37579Labels = mixedMoment B raw37579step0 raw37579step0Labels := by
      have hz : ∀ j, raw37579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37579step0 = (fun i j => raw37579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37579step0 raw37579; decide +kernel
      have hl : raw37579step0Labels = raw37579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37579 raw37579Labels permutation434 hz
    mixedMoment B raw37579step0 raw37579step0Labels = mixedMoment B raw37579step1 raw37579step1Labels := by
      have hz : ∀ j, raw37579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37579step1 = (fun i j => raw37579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37579step1 raw37579step0; decide +kernel
      have hl : raw37579step1Labels = raw37579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37579step0 raw37579step0Labels permutation80 hz
    mixedMoment B raw37579step1 raw37579step1Labels = mixedMoment B raw37579step2 raw37579step2Labels := by
      have ha : raw37579step2 = -raw37579step1 := by apply Matrix.ext; change ∀ i j, raw37579step2 i j = -(raw37579step1 i j); unfold raw37579step2 raw37579step1; decide +kernel
      have hl : raw37579step2Labels = raw37579step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw37580 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37580 raw37580Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw37580 raw37580Labels = mixedMoment B raw37580step0 raw37580step0Labels := by
      have hz : ∀ j, raw37580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37580step0 = (fun i j => raw37580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37580step0 raw37580; decide +kernel
      have hl : raw37580step0Labels = raw37580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37580 raw37580Labels permutation434 hz
    mixedMoment B raw37580step0 raw37580step0Labels = mixedMoment B raw37580step1 raw37580step1Labels := by
      have ha : raw37580step1 = (fun i j => raw37580step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37580step1 raw37580step0; decide +kernel
      have hl : raw37580step1Labels = raw37580step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37580step0 raw37580step0Labels permutation32 permutation4
    mixedMoment B raw37580step1 raw37580step1Labels = mixedMoment B raw37580step2 raw37580step2Labels := by
      have ha : raw37580step2 = -raw37580step1 := by apply Matrix.ext; change ∀ i j, raw37580step2 i j = -(raw37580step1 i j); unfold raw37580step2 raw37580step1; decide +kernel
      have hl : raw37580step2Labels = raw37580step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw37581 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37581 raw37581Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw37581 raw37581Labels = mixedMoment B raw37581step0 raw37581step0Labels := by
      have hz : ∀ j, raw37581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37581step0 = (fun i j => raw37581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37581step0 raw37581; decide +kernel
      have hl : raw37581step0Labels = raw37581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37581 raw37581Labels permutation346 hz
    mixedMoment B raw37581step0 raw37581step0Labels = mixedMoment B raw37581step1 raw37581step1Labels := by
      have ha : raw37581step1 = (fun i j => raw37581step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37581step1 raw37581step0; decide +kernel
      have hl : raw37581step1Labels = raw37581step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37581step0 raw37581step0Labels permutation32 permutation4
    mixedMoment B raw37581step1 raw37581step1Labels = mixedMoment B raw37581step2 raw37581step2Labels := by
      have ha : raw37581step2 = -raw37581step1 := by apply Matrix.ext; change ∀ i j, raw37581step2 i j = -(raw37581step1 i j); unfold raw37581step2 raw37581step1; decide +kernel
      have hl : raw37581step2Labels = raw37581step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw37582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw37582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37582 raw37582Labels = mixedMoment B node1570 node1570Labels := by
  calc
    mixedMoment B raw37582 raw37582Labels = mixedMoment B raw37582step0 raw37582step0Labels := by
      have hz : ∀ j, raw37582 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37582step0 = (fun i j => raw37582 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37582step0 raw37582; decide +kernel
      have hl : raw37582step0Labels = raw37582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37582 raw37582Labels permutation434 hz
    mixedMoment B raw37582step0 raw37582step0Labels = mixedMoment B raw37582step1 raw37582step1Labels := by
      have ha : raw37582step1 = (fun i j => raw37582step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37582step1 raw37582step0; decide +kernel
      have hl : raw37582step1Labels = raw37582step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37582step0 raw37582step0Labels permutation33 permutation4
    mixedMoment B raw37582step1 raw37582step1Labels = mixedMoment B raw37582step2 raw37582step2Labels := by
      have ha : raw37582step2 = -raw37582step1 := by apply Matrix.ext; change ∀ i j, raw37582step2 i j = -(raw37582step1 i j); unfold raw37582step2 raw37582step1; decide +kernel
      have hl : raw37582step2Labels = raw37582step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1570 node1570Labels := by rfl

def raw37583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw37583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37583step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37583step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37583 raw37583Labels = mixedMoment B node1570 node1570Labels := by
  calc
    mixedMoment B raw37583 raw37583Labels = mixedMoment B raw37583step0 raw37583step0Labels := by
      have hz : ∀ j, raw37583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37583step0 = (fun i j => raw37583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37583step0 raw37583; decide +kernel
      have hl : raw37583step0Labels = raw37583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37583 raw37583Labels permutation346 hz
    mixedMoment B raw37583step0 raw37583step0Labels = mixedMoment B raw37583step1 raw37583step1Labels := by
      have ha : raw37583step1 = (fun i j => raw37583step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37583step1 raw37583step0; decide +kernel
      have hl : raw37583step1Labels = raw37583step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37583step0 raw37583step0Labels permutation33 permutation4
    mixedMoment B raw37583step1 raw37583step1Labels = mixedMoment B raw37583step2 raw37583step2Labels := by
      have ha : raw37583step2 = -raw37583step1 := by apply Matrix.ext; change ∀ i j, raw37583step2 i j = -(raw37583step1 i j); unfold raw37583step2 raw37583step1; decide +kernel
      have hl : raw37583step2Labels = raw37583step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1570 node1570Labels := by rfl

def raw37584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, -1, 3]]
def raw37584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![-2, -1, 3]]
def raw37584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -3, 2], ![-2, -1, 3]]
def raw37584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw37584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37584step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 2, -3], ![3, -1, -2]]
def raw37584step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37584 raw37584Labels = mixedMoment B node1577 node1577Labels := by
  calc
    mixedMoment B raw37584 raw37584Labels = mixedMoment B raw37584step0 raw37584step0Labels := by
      have hz : ∀ j, raw37584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37584step0 = (fun i j => raw37584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37584step0 raw37584; decide +kernel
      have hl : raw37584step0Labels = raw37584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37584 raw37584Labels permutation434 hz
    mixedMoment B raw37584step0 raw37584step0Labels = mixedMoment B raw37584step1 raw37584step1Labels := by
      have hz : ∀ j, raw37584step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37584step1 = (fun i j => raw37584step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37584step1 raw37584step0; decide +kernel
      have hl : raw37584step1Labels = raw37584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37584step0 raw37584step0Labels permutation80 hz
    mixedMoment B raw37584step1 raw37584step1Labels = mixedMoment B raw37584step2 raw37584step2Labels := by
      have ha : raw37584step2 = (fun i j => raw37584step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37584step2 raw37584step1; decide +kernel
      have hl : raw37584step2Labels = raw37584step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37584step1 raw37584step1Labels permutation9 permutation4
    mixedMoment B raw37584step2 raw37584step2Labels = mixedMoment B raw37584step3 raw37584step3Labels := by
      have ha : raw37584step3 = -raw37584step2 := by apply Matrix.ext; change ∀ i j, raw37584step3 i j = -(raw37584step2 i j); unfold raw37584step3 raw37584step2; decide +kernel
      have hl : raw37584step3Labels = raw37584step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1577 node1577Labels := by rfl

def raw37585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -2, 3]]
def raw37585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw37585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37585step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37585step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37585 raw37585Labels = mixedMoment B node1579 node1579Labels := by
  calc
    mixedMoment B raw37585 raw37585Labels = mixedMoment B raw37585step0 raw37585step0Labels := by
      have hz : ∀ j, raw37585 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37585step0 = (fun i j => raw37585 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37585step0 raw37585; decide +kernel
      have hl : raw37585step0Labels = raw37585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37585 raw37585Labels permutation434 hz
    mixedMoment B raw37585step0 raw37585step0Labels = mixedMoment B raw37585step1 raw37585step1Labels := by
      have hz : ∀ j, raw37585step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37585step1 = (fun i j => raw37585step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37585step1 raw37585step0; decide +kernel
      have hl : raw37585step1Labels = raw37585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37585step0 raw37585step0Labels permutation80 hz
    mixedMoment B raw37585step1 raw37585step1Labels = mixedMoment B raw37585step2 raw37585step2Labels := by
      have ha : raw37585step2 = (fun i j => raw37585step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37585step2 raw37585step1; decide +kernel
      have hl : raw37585step2Labels = raw37585step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37585step1 raw37585step1Labels permutation8 permutation4
    mixedMoment B raw37585step2 raw37585step2Labels = mixedMoment B raw37585step3 raw37585step3Labels := by
      have ha : raw37585step3 = -raw37585step2 := by apply Matrix.ext; change ∀ i j, raw37585step3 i j = -(raw37585step2 i j); unfold raw37585step3 raw37585step2; decide +kernel
      have hl : raw37585step3Labels = raw37585step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1579 node1579Labels := by rfl

def raw37586 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, -2, 2], ![-1, -2, 3]]
def raw37586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw37586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37586step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37586 raw37586Labels = mixedMoment B node3237 node3237Labels := by
  calc
    mixedMoment B raw37586 raw37586Labels = mixedMoment B raw37586step0 raw37586step0Labels := by
      have hz : ∀ j, raw37586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37586step0 = (fun i j => raw37586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37586step0 raw37586; decide +kernel
      have hl : raw37586step0Labels = raw37586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37586 raw37586Labels permutation434 hz
    mixedMoment B raw37586step0 raw37586step0Labels = mixedMoment B raw37586step1 raw37586step1Labels := by
      have hz : ∀ j, raw37586step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37586step1 = (fun i j => raw37586step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37586step1 raw37586step0; decide +kernel
      have hl : raw37586step1Labels = raw37586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37586step0 raw37586step0Labels permutation80 hz
    mixedMoment B raw37586step1 raw37586step1Labels = mixedMoment B raw37586step2 raw37586step2Labels := by
      have ha : raw37586step2 = (fun i j => raw37586step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37586step2 raw37586step1; decide +kernel
      have hl : raw37586step2Labels = raw37586step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37586step1 raw37586step1Labels permutation8 permutation4
    mixedMoment B raw37586step2 raw37586step2Labels = mixedMoment B raw37586step3 raw37586step3Labels := by
      have ha : raw37586step3 = -raw37586step2 := by apply Matrix.ext; change ∀ i j, raw37586step3 i j = -(raw37586step2 i j); unfold raw37586step3 raw37586step2; decide +kernel
      have hl : raw37586step3Labels = raw37586step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3237 node3237Labels := by rfl

def raw37587 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw37587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37587 raw37587Labels = mixedMoment B node3252 node3252Labels := by
  calc
    mixedMoment B raw37587 raw37587Labels = mixedMoment B raw37587step0 raw37587step0Labels := by
      have hz : ∀ j, raw37587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37587step0 = (fun i j => raw37587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37587step0 raw37587; decide +kernel
      have hl : raw37587step0Labels = raw37587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37587 raw37587Labels permutation434 hz
    mixedMoment B raw37587step0 raw37587step0Labels = mixedMoment B raw37587step1 raw37587step1Labels := by
      have ha : raw37587step1 = (fun i j => raw37587step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37587step1 raw37587step0; decide +kernel
      have hl : raw37587step1Labels = raw37587step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37587step0 raw37587step0Labels permutation32 permutation4
    mixedMoment B raw37587step1 raw37587step1Labels = mixedMoment B raw37587step2 raw37587step2Labels := by
      have ha : raw37587step2 = -raw37587step1 := by apply Matrix.ext; change ∀ i j, raw37587step2 i j = -(raw37587step1 i j); unfold raw37587step2 raw37587step1; decide +kernel
      have hl : raw37587step2Labels = raw37587step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3252 node3252Labels := by rfl

def raw37588 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw37588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37588 raw37588Labels = mixedMoment B node3252 node3252Labels := by
  calc
    mixedMoment B raw37588 raw37588Labels = mixedMoment B raw37588step0 raw37588step0Labels := by
      have hz : ∀ j, raw37588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37588step0 = (fun i j => raw37588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37588step0 raw37588; decide +kernel
      have hl : raw37588step0Labels = raw37588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37588 raw37588Labels permutation346 hz
    mixedMoment B raw37588step0 raw37588step0Labels = mixedMoment B raw37588step1 raw37588step1Labels := by
      have ha : raw37588step1 = (fun i j => raw37588step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37588step1 raw37588step0; decide +kernel
      have hl : raw37588step1Labels = raw37588step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37588step0 raw37588step0Labels permutation32 permutation4
    mixedMoment B raw37588step1 raw37588step1Labels = mixedMoment B raw37588step2 raw37588step2Labels := by
      have ha : raw37588step2 = -raw37588step1 := by apply Matrix.ext; change ∀ i j, raw37588step2 i j = -(raw37588step1 i j); unfold raw37588step2 raw37588step1; decide +kernel
      have hl : raw37588step2Labels = raw37588step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3252 node3252Labels := by rfl

def raw37589 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37589 raw37589Labels = mixedMoment B node1569 node1569Labels := by
  calc
    mixedMoment B raw37589 raw37589Labels = mixedMoment B raw37589step0 raw37589step0Labels := by
      have hz : ∀ j, raw37589 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37589step0 = (fun i j => raw37589 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37589step0 raw37589; decide +kernel
      have hl : raw37589step0Labels = raw37589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37589 raw37589Labels permutation434 hz
    mixedMoment B raw37589step0 raw37589step0Labels = mixedMoment B raw37589step1 raw37589step1Labels := by
      have ha : raw37589step1 = (fun i j => raw37589step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37589step1 raw37589step0; decide +kernel
      have hl : raw37589step1Labels = raw37589step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37589step0 raw37589step0Labels permutation32 permutation4
    mixedMoment B raw37589step1 raw37589step1Labels = mixedMoment B raw37589step2 raw37589step2Labels := by
      have ha : raw37589step2 = -raw37589step1 := by apply Matrix.ext; change ∀ i j, raw37589step2 i j = -(raw37589step1 i j); unfold raw37589step2 raw37589step1; decide +kernel
      have hl : raw37589step2Labels = raw37589step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1569 node1569Labels := by rfl

def raw37590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37590 raw37590Labels = mixedMoment B node1569 node1569Labels := by
  calc
    mixedMoment B raw37590 raw37590Labels = mixedMoment B raw37590step0 raw37590step0Labels := by
      have hz : ∀ j, raw37590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37590step0 = (fun i j => raw37590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37590step0 raw37590; decide +kernel
      have hl : raw37590step0Labels = raw37590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37590 raw37590Labels permutation346 hz
    mixedMoment B raw37590step0 raw37590step0Labels = mixedMoment B raw37590step1 raw37590step1Labels := by
      have ha : raw37590step1 = (fun i j => raw37590step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37590step1 raw37590step0; decide +kernel
      have hl : raw37590step1Labels = raw37590step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37590step0 raw37590step0Labels permutation32 permutation4
    mixedMoment B raw37590step1 raw37590step1Labels = mixedMoment B raw37590step2 raw37590step2Labels := by
      have ha : raw37590step2 = -raw37590step1 := by apply Matrix.ext; change ∀ i j, raw37590step2 i j = -(raw37590step1 i j); unfold raw37590step2 raw37590step1; decide +kernel
      have hl : raw37590step2Labels = raw37590step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1569 node1569Labels := by rfl

def raw37591 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![-1, -1, 2], ![0, -3, 3]]
def raw37591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw37591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37591step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![3, 0, -3]]
def raw37591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37591 raw37591Labels = mixedMoment B node1576 node1576Labels := by
  calc
    mixedMoment B raw37591 raw37591Labels = mixedMoment B raw37591step0 raw37591step0Labels := by
      have hz : ∀ j, raw37591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37591step0 = (fun i j => raw37591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37591step0 raw37591; decide +kernel
      have hl : raw37591step0Labels = raw37591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37591 raw37591Labels permutation434 hz
    mixedMoment B raw37591step0 raw37591step0Labels = mixedMoment B raw37591step1 raw37591step1Labels := by
      have hz : ∀ j, raw37591step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37591step1 = (fun i j => raw37591step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37591step1 raw37591step0; decide +kernel
      have hl : raw37591step1Labels = raw37591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37591step0 raw37591step0Labels permutation80 hz
    mixedMoment B raw37591step1 raw37591step1Labels = mixedMoment B raw37591step2 raw37591step2Labels := by
      have ha : raw37591step2 = (fun i j => raw37591step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37591step2 raw37591step1; decide +kernel
      have hl : raw37591step2Labels = raw37591step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37591step1 raw37591step1Labels permutation8 permutation4
    mixedMoment B raw37591step2 raw37591step2Labels = mixedMoment B raw37591step3 raw37591step3Labels := by
      have ha : raw37591step3 = -raw37591step2 := by apply Matrix.ext; change ∀ i j, raw37591step3 i j = -(raw37591step2 i j); unfold raw37591step3 raw37591step2; decide +kernel
      have hl : raw37591step3Labels = raw37591step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1576 node1576Labels := by rfl

def raw37592 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![-1, -1, 2], ![0, -3, 3]]
def raw37592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, -1, -1], ![2, 2, -4]]
def raw37592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37592 raw37592Labels = mixedMoment B node1858 node1858Labels := by
  calc
    mixedMoment B raw37592 raw37592Labels = mixedMoment B raw37592step0 raw37592step0Labels := by
      have hz : ∀ j, raw37592 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37592step0 = (fun i j => raw37592 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37592step0 raw37592; decide +kernel
      have hl : raw37592step0Labels = raw37592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37592 raw37592Labels permutation434 hz
    mixedMoment B raw37592step0 raw37592step0Labels = mixedMoment B raw37592step1 raw37592step1Labels := by
      have hz : ∀ j, raw37592step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37592step1 = (fun i j => raw37592step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37592step1 raw37592step0; decide +kernel
      have hl : raw37592step1Labels = raw37592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37592step0 raw37592step0Labels permutation80 hz
    mixedMoment B raw37592step1 raw37592step1Labels = mixedMoment B raw37592step2 raw37592step2Labels := by
      have ha : raw37592step2 = (fun i j => raw37592step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37592step2 raw37592step1; decide +kernel
      have hl : raw37592step2Labels = raw37592step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37592step1 raw37592step1Labels permutation31 permutation4
    _ = mixedMoment B node1858 node1858Labels := by rfl

def raw37593 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37593step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37593 raw37593Labels = mixedMoment B node1849 node1849Labels := by
  calc
    mixedMoment B raw37593 raw37593Labels = mixedMoment B raw37593step0 raw37593step0Labels := by
      have hz : ∀ j, raw37593 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37593step0 = (fun i j => raw37593 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37593step0 raw37593; decide +kernel
      have hl : raw37593step0Labels = raw37593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37593 raw37593Labels permutation434 hz
    mixedMoment B raw37593step0 raw37593step0Labels = mixedMoment B raw37593step1 raw37593step1Labels := by
      have ha : raw37593step1 = (fun i j => raw37593step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37593step1 raw37593step0; decide +kernel
      have hl : raw37593step1Labels = raw37593step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37593step0 raw37593step0Labels permutation151 permutation4
    _ = mixedMoment B node1849 node1849Labels := by rfl

def raw37594 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37594 raw37594Labels = mixedMoment B node1849 node1849Labels := by
  calc
    mixedMoment B raw37594 raw37594Labels = mixedMoment B raw37594step0 raw37594step0Labels := by
      have hz : ∀ j, raw37594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37594step0 = (fun i j => raw37594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37594step0 raw37594; decide +kernel
      have hl : raw37594step0Labels = raw37594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37594 raw37594Labels permutation346 hz
    mixedMoment B raw37594step0 raw37594step0Labels = mixedMoment B raw37594step1 raw37594step1Labels := by
      have ha : raw37594step1 = (fun i j => raw37594step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37594step1 raw37594step0; decide +kernel
      have hl : raw37594step1Labels = raw37594step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37594step0 raw37594step0Labels permutation151 permutation4
    _ = mixedMoment B node1849 node1849Labels := by rfl

def raw37595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37595Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw37595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw37595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37595 raw37595Labels = mixedMoment B node1562 node1562Labels := by
  calc
    mixedMoment B raw37595 raw37595Labels = mixedMoment B raw37595step0 raw37595step0Labels := by
      have hz : ∀ j, raw37595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37595step0 = (fun i j => raw37595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37595step0 raw37595; decide +kernel
      have hl : raw37595step0Labels = raw37595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37595 raw37595Labels permutation434 hz
    mixedMoment B raw37595step0 raw37595step0Labels = mixedMoment B raw37595step1 raw37595step1Labels := by
      have ha : raw37595step1 = (fun i j => raw37595step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37595step1 raw37595step0; decide +kernel
      have hl : raw37595step1Labels = raw37595step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37595step0 raw37595step0Labels permutation34 permutation4
    mixedMoment B raw37595step1 raw37595step1Labels = mixedMoment B raw37595step2 raw37595step2Labels := by
      have ha : raw37595step2 = -raw37595step1 := by apply Matrix.ext; change ∀ i j, raw37595step2 i j = -(raw37595step1 i j); unfold raw37595step2 raw37595step1; decide +kernel
      have hl : raw37595step2Labels = raw37595step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1562 node1562Labels := by rfl

def raw37596 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw37596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw37596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37596 raw37596Labels = mixedMoment B node1562 node1562Labels := by
  calc
    mixedMoment B raw37596 raw37596Labels = mixedMoment B raw37596step0 raw37596step0Labels := by
      have hz : ∀ j, raw37596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37596step0 = (fun i j => raw37596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37596step0 raw37596; decide +kernel
      have hl : raw37596step0Labels = raw37596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37596 raw37596Labels permutation346 hz
    mixedMoment B raw37596step0 raw37596step0Labels = mixedMoment B raw37596step1 raw37596step1Labels := by
      have ha : raw37596step1 = (fun i j => raw37596step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37596step1 raw37596step0; decide +kernel
      have hl : raw37596step1Labels = raw37596step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37596step0 raw37596step0Labels permutation34 permutation4
    mixedMoment B raw37596step1 raw37596step1Labels = mixedMoment B raw37596step2 raw37596step2Labels := by
      have ha : raw37596step2 = -raw37596step1 := by apply Matrix.ext; change ∀ i j, raw37596step2 i j = -(raw37596step1 i j); unfold raw37596step2 raw37596step1; decide +kernel
      have hl : raw37596step2Labels = raw37596step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1562 node1562Labels := by rfl

def raw37597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -4, 3]]
def raw37597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -4, 3]]
def raw37597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![-2, 0, 2], ![1, -4, 3]]
def raw37597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![3, 1, -4]]
def raw37597step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37597 raw37597Labels = mixedMoment B node961 node961Labels := by
  calc
    mixedMoment B raw37597 raw37597Labels = mixedMoment B raw37597step0 raw37597step0Labels := by
      have hz : ∀ j, raw37597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37597step0 = (fun i j => raw37597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37597step0 raw37597; decide +kernel
      have hl : raw37597step0Labels = raw37597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37597 raw37597Labels permutation434 hz
    mixedMoment B raw37597step0 raw37597step0Labels = mixedMoment B raw37597step1 raw37597step1Labels := by
      have hz : ∀ j, raw37597step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37597step1 = (fun i j => raw37597step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37597step1 raw37597step0; decide +kernel
      have hl : raw37597step1Labels = raw37597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37597step0 raw37597step0Labels permutation80 hz
    mixedMoment B raw37597step1 raw37597step1Labels = mixedMoment B raw37597step2 raw37597step2Labels := by
      have ha : raw37597step2 = (fun i j => raw37597step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37597step2 raw37597step1; decide +kernel
      have hl : raw37597step2Labels = raw37597step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37597step1 raw37597step1Labels permutation31 permutation4
    _ = mixedMoment B node961 node961Labels := by rfl

def raw37598 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, -2, 2], ![-2, -1, 3]]
def raw37598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw37598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37598step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37598step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37598 raw37598Labels = mixedMoment B node844 node844Labels := by
  calc
    mixedMoment B raw37598 raw37598Labels = mixedMoment B raw37598step0 raw37598step0Labels := by
      have hz : ∀ j, raw37598 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37598step0 = (fun i j => raw37598 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37598step0 raw37598; decide +kernel
      have hl : raw37598step0Labels = raw37598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37598 raw37598Labels permutation434 hz
    mixedMoment B raw37598step0 raw37598step0Labels = mixedMoment B raw37598step1 raw37598step1Labels := by
      have hz : ∀ j, raw37598step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37598step1 = (fun i j => raw37598step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37598step1 raw37598step0; decide +kernel
      have hl : raw37598step1Labels = raw37598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37598step0 raw37598step0Labels permutation80 hz
    mixedMoment B raw37598step1 raw37598step1Labels = mixedMoment B raw37598step2 raw37598step2Labels := by
      have ha : raw37598step2 = (fun i j => raw37598step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37598step2 raw37598step1; decide +kernel
      have hl : raw37598step2Labels = raw37598step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37598step1 raw37598step1Labels permutation9 permutation4
    mixedMoment B raw37598step2 raw37598step2Labels = mixedMoment B raw37598step3 raw37598step3Labels := by
      have ha : raw37598step3 = -raw37598step2 := by apply Matrix.ext; change ∀ i j, raw37598step3 i j = -(raw37598step2 i j); unfold raw37598step3 raw37598step2; decide +kernel
      have hl : raw37598step3Labels = raw37598step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node844 node844Labels := by rfl

def raw37599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw37599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37599 raw37599Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw37599 raw37599Labels = mixedMoment B raw37599step0 raw37599step0Labels := by
      have hz : ∀ j, raw37599 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37599step0 = (fun i j => raw37599 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37599step0 raw37599; decide +kernel
      have hl : raw37599step0Labels = raw37599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37599 raw37599Labels permutation434 hz
    mixedMoment B raw37599step0 raw37599step0Labels = mixedMoment B raw37599step1 raw37599step1Labels := by
      have ha : raw37599step1 = (fun i j => raw37599step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37599step1 raw37599step0; decide +kernel
      have hl : raw37599step1Labels = raw37599step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37599step0 raw37599step0Labels permutation33 permutation4
    mixedMoment B raw37599step1 raw37599step1Labels = mixedMoment B raw37599step2 raw37599step2Labels := by
      have ha : raw37599step2 = -raw37599step1 := by apply Matrix.ext; change ∀ i j, raw37599step2 i j = -(raw37599step1 i j); unfold raw37599step2 raw37599step1; decide +kernel
      have hl : raw37599step2Labels = raw37599step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node764 node764Labels := by rfl

def raw37600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw37600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37600 raw37600Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw37600 raw37600Labels = mixedMoment B raw37600step0 raw37600step0Labels := by
      have hz : ∀ j, raw37600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37600step0 = (fun i j => raw37600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37600step0 raw37600; decide +kernel
      have hl : raw37600step0Labels = raw37600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37600 raw37600Labels permutation346 hz
    mixedMoment B raw37600step0 raw37600step0Labels = mixedMoment B raw37600step1 raw37600step1Labels := by
      have ha : raw37600step1 = (fun i j => raw37600step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37600step1 raw37600step0; decide +kernel
      have hl : raw37600step1Labels = raw37600step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37600step0 raw37600step0Labels permutation33 permutation4
    mixedMoment B raw37600step1 raw37600step1Labels = mixedMoment B raw37600step2 raw37600step2Labels := by
      have ha : raw37600step2 = -raw37600step1 := by apply Matrix.ext; change ∀ i j, raw37600step2 i j = -(raw37600step1 i j); unfold raw37600step2 raw37600step1; decide +kernel
      have hl : raw37600step2Labels = raw37600step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node764 node764Labels := by rfl

def raw37601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, -1, 3]]
def raw37601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![-2, -1, 3]]
def raw37601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -3, 2], ![-2, -1, 3]]
def raw37601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw37601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw37601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37601 raw37601Labels = mixedMoment B node773 node773Labels := by
  calc
    mixedMoment B raw37601 raw37601Labels = mixedMoment B raw37601step0 raw37601step0Labels := by
      have hz : ∀ j, raw37601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37601step0 = (fun i j => raw37601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37601step0 raw37601; decide +kernel
      have hl : raw37601step0Labels = raw37601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37601 raw37601Labels permutation434 hz
    mixedMoment B raw37601step0 raw37601step0Labels = mixedMoment B raw37601step1 raw37601step1Labels := by
      have hz : ∀ j, raw37601step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37601step1 = (fun i j => raw37601step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37601step1 raw37601step0; decide +kernel
      have hl : raw37601step1Labels = raw37601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37601step0 raw37601step0Labels permutation80 hz
    mixedMoment B raw37601step1 raw37601step1Labels = mixedMoment B raw37601step2 raw37601step2Labels := by
      have ha : raw37601step2 = (fun i j => raw37601step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37601step2 raw37601step1; decide +kernel
      have hl : raw37601step2Labels = raw37601step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37601step1 raw37601step1Labels permutation9 permutation4
    mixedMoment B raw37601step2 raw37601step2Labels = mixedMoment B raw37601step3 raw37601step3Labels := by
      have ha : raw37601step3 = -raw37601step2 := by apply Matrix.ext; change ∀ i j, raw37601step3 i j = -(raw37601step2 i j); unfold raw37601step3 raw37601step2; decide +kernel
      have hl : raw37601step3Labels = raw37601step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node773 node773Labels := by rfl

def raw37602 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -2, 3]]
def raw37602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw37602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37602step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37602step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37602 raw37602Labels = mixedMoment B node775 node775Labels := by
  calc
    mixedMoment B raw37602 raw37602Labels = mixedMoment B raw37602step0 raw37602step0Labels := by
      have hz : ∀ j, raw37602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37602step0 = (fun i j => raw37602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37602step0 raw37602; decide +kernel
      have hl : raw37602step0Labels = raw37602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37602 raw37602Labels permutation434 hz
    mixedMoment B raw37602step0 raw37602step0Labels = mixedMoment B raw37602step1 raw37602step1Labels := by
      have hz : ∀ j, raw37602step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37602step1 = (fun i j => raw37602step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37602step1 raw37602step0; decide +kernel
      have hl : raw37602step1Labels = raw37602step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37602step0 raw37602step0Labels permutation80 hz
    mixedMoment B raw37602step1 raw37602step1Labels = mixedMoment B raw37602step2 raw37602step2Labels := by
      have ha : raw37602step2 = (fun i j => raw37602step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37602step2 raw37602step1; decide +kernel
      have hl : raw37602step2Labels = raw37602step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37602step1 raw37602step1Labels permutation8 permutation4
    mixedMoment B raw37602step2 raw37602step2Labels = mixedMoment B raw37602step3 raw37602step3Labels := by
      have ha : raw37602step3 = -raw37602step2 := by apply Matrix.ext; change ∀ i j, raw37602step3 i j = -(raw37602step2 i j); unfold raw37602step3 raw37602step2; decide +kernel
      have hl : raw37602step3Labels = raw37602step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node775 node775Labels := by rfl

def raw37603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw37603step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37603 raw37603Labels = mixedMoment B node1591 node1591Labels := by
  calc
    mixedMoment B raw37603 raw37603Labels = mixedMoment B raw37603step0 raw37603step0Labels := by
      have hz : ∀ j, raw37603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37603step0 = (fun i j => raw37603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37603step0 raw37603; decide +kernel
      have hl : raw37603step0Labels = raw37603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37603 raw37603Labels permutation434 hz
    mixedMoment B raw37603step0 raw37603step0Labels = mixedMoment B raw37603step1 raw37603step1Labels := by
      have ha : raw37603step1 = (fun i j => raw37603step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37603step1 raw37603step0; decide +kernel
      have hl : raw37603step1Labels = raw37603step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37603step0 raw37603step0Labels permutation38 permutation4
    mixedMoment B raw37603step1 raw37603step1Labels = mixedMoment B raw37603step2 raw37603step2Labels := by
      have ha : raw37603step2 = -raw37603step1 := by apply Matrix.ext; change ∀ i j, raw37603step2 i j = -(raw37603step1 i j); unfold raw37603step2 raw37603step1; decide +kernel
      have hl : raw37603step2Labels = raw37603step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1591 node1591Labels := by rfl

def raw37604 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37604step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw37604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37604 raw37604Labels = mixedMoment B node1591 node1591Labels := by
  calc
    mixedMoment B raw37604 raw37604Labels = mixedMoment B raw37604step0 raw37604step0Labels := by
      have hz : ∀ j, raw37604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37604step0 = (fun i j => raw37604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37604step0 raw37604; decide +kernel
      have hl : raw37604step0Labels = raw37604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37604 raw37604Labels permutation346 hz
    mixedMoment B raw37604step0 raw37604step0Labels = mixedMoment B raw37604step1 raw37604step1Labels := by
      have ha : raw37604step1 = (fun i j => raw37604step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37604step1 raw37604step0; decide +kernel
      have hl : raw37604step1Labels = raw37604step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37604step0 raw37604step0Labels permutation38 permutation4
    mixedMoment B raw37604step1 raw37604step1Labels = mixedMoment B raw37604step2 raw37604step2Labels := by
      have ha : raw37604step2 = -raw37604step1 := by apply Matrix.ext; change ∀ i j, raw37604step2 i j = -(raw37604step1 i j); unfold raw37604step2 raw37604step1; decide +kernel
      have hl : raw37604step2Labels = raw37604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1591 node1591Labels := by rfl

def raw37605 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw37605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37605step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37605step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37605 raw37605Labels = mixedMoment B node843 node843Labels := by
  calc
    mixedMoment B raw37605 raw37605Labels = mixedMoment B raw37605step0 raw37605step0Labels := by
      have hz : ∀ j, raw37605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37605step0 = (fun i j => raw37605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37605step0 raw37605; decide +kernel
      have hl : raw37605step0Labels = raw37605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37605 raw37605Labels permutation434 hz
    mixedMoment B raw37605step0 raw37605step0Labels = mixedMoment B raw37605step1 raw37605step1Labels := by
      have hz : ∀ j, raw37605step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37605step1 = (fun i j => raw37605step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37605step1 raw37605step0; decide +kernel
      have hl : raw37605step1Labels = raw37605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37605step0 raw37605step0Labels permutation80 hz
    mixedMoment B raw37605step1 raw37605step1Labels = mixedMoment B raw37605step2 raw37605step2Labels := by
      have ha : raw37605step2 = (fun i j => raw37605step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37605step2 raw37605step1; decide +kernel
      have hl : raw37605step2Labels = raw37605step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37605step1 raw37605step1Labels permutation8 permutation4
    mixedMoment B raw37605step2 raw37605step2Labels = mixedMoment B raw37605step3 raw37605step3Labels := by
      have ha : raw37605step3 = -raw37605step2 := by apply Matrix.ext; change ∀ i j, raw37605step3 i j = -(raw37605step2 i j); unfold raw37605step3 raw37605step2; decide +kernel
      have hl : raw37605step3Labels = raw37605step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node843 node843Labels := by rfl

def raw37606 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37606 raw37606Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw37606 raw37606Labels = mixedMoment B raw37606step0 raw37606step0Labels := by
      have hz : ∀ j, raw37606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37606step0 = (fun i j => raw37606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37606step0 raw37606; decide +kernel
      have hl : raw37606step0Labels = raw37606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37606 raw37606Labels permutation434 hz
    mixedMoment B raw37606step0 raw37606step0Labels = mixedMoment B raw37606step1 raw37606step1Labels := by
      have ha : raw37606step1 = (fun i j => raw37606step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37606step1 raw37606step0; decide +kernel
      have hl : raw37606step1Labels = raw37606step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37606step0 raw37606step0Labels permutation32 permutation4
    mixedMoment B raw37606step1 raw37606step1Labels = mixedMoment B raw37606step2 raw37606step2Labels := by
      have ha : raw37606step2 = -raw37606step1 := by apply Matrix.ext; change ∀ i j, raw37606step2 i j = -(raw37606step1 i j); unfold raw37606step2 raw37606step1; decide +kernel
      have hl : raw37606step2Labels = raw37606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node763 node763Labels := by rfl

def raw37607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37607 raw37607Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw37607 raw37607Labels = mixedMoment B raw37607step0 raw37607step0Labels := by
      have hz : ∀ j, raw37607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37607step0 = (fun i j => raw37607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37607step0 raw37607; decide +kernel
      have hl : raw37607step0Labels = raw37607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37607 raw37607Labels permutation346 hz
    mixedMoment B raw37607step0 raw37607step0Labels = mixedMoment B raw37607step1 raw37607step1Labels := by
      have ha : raw37607step1 = (fun i j => raw37607step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37607step1 raw37607step0; decide +kernel
      have hl : raw37607step1Labels = raw37607step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37607step0 raw37607step0Labels permutation32 permutation4
    mixedMoment B raw37607step1 raw37607step1Labels = mixedMoment B raw37607step2 raw37607step2Labels := by
      have ha : raw37607step2 = -raw37607step1 := by apply Matrix.ext; change ∀ i j, raw37607step2 i j = -(raw37607step1 i j); unfold raw37607step2 raw37607step1; decide +kernel
      have hl : raw37607step2Labels = raw37607step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node763 node763Labels := by rfl

def raw37608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![-1, -1, 2], ![0, -3, 3]]
def raw37608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw37608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37608step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw37608step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37608 raw37608Labels = mixedMoment B node772 node772Labels := by
  calc
    mixedMoment B raw37608 raw37608Labels = mixedMoment B raw37608step0 raw37608step0Labels := by
      have hz : ∀ j, raw37608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37608step0 = (fun i j => raw37608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37608step0 raw37608; decide +kernel
      have hl : raw37608step0Labels = raw37608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37608 raw37608Labels permutation434 hz
    mixedMoment B raw37608step0 raw37608step0Labels = mixedMoment B raw37608step1 raw37608step1Labels := by
      have hz : ∀ j, raw37608step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37608step1 = (fun i j => raw37608step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37608step1 raw37608step0; decide +kernel
      have hl : raw37608step1Labels = raw37608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37608step0 raw37608step0Labels permutation80 hz
    mixedMoment B raw37608step1 raw37608step1Labels = mixedMoment B raw37608step2 raw37608step2Labels := by
      have ha : raw37608step2 = (fun i j => raw37608step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37608step2 raw37608step1; decide +kernel
      have hl : raw37608step2Labels = raw37608step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37608step1 raw37608step1Labels permutation8 permutation4
    mixedMoment B raw37608step2 raw37608step2Labels = mixedMoment B raw37608step3 raw37608step3Labels := by
      have ha : raw37608step3 = -raw37608step2 := by apply Matrix.ext; change ∀ i j, raw37608step3 i j = -(raw37608step2 i j); unfold raw37608step3 raw37608step2; decide +kernel
      have hl : raw37608step3Labels = raw37608step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node772 node772Labels := by rfl

def raw37609 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw37609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw37609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37609 raw37609Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw37609 raw37609Labels = mixedMoment B raw37609step0 raw37609step0Labels := by
      have hz : ∀ j, raw37609 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37609step0 = (fun i j => raw37609 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37609step0 raw37609; decide +kernel
      have hl : raw37609step0Labels = raw37609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37609 raw37609Labels permutation434 hz
    mixedMoment B raw37609step0 raw37609step0Labels = mixedMoment B raw37609step1 raw37609step1Labels := by
      have ha : raw37609step1 = (fun i j => raw37609step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37609step1 raw37609step0; decide +kernel
      have hl : raw37609step1Labels = raw37609step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37609step0 raw37609step0Labels permutation38 permutation4
    mixedMoment B raw37609step1 raw37609step1Labels = mixedMoment B raw37609step2 raw37609step2Labels := by
      have ha : raw37609step2 = -raw37609step1 := by apply Matrix.ext; change ∀ i j, raw37609step2 i j = -(raw37609step1 i j); unfold raw37609step2 raw37609step1; decide +kernel
      have hl : raw37609step2Labels = raw37609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1590 node1590Labels := by rfl

def raw37610 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw37610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw37610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37610 raw37610Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw37610 raw37610Labels = mixedMoment B raw37610step0 raw37610step0Labels := by
      have hz : ∀ j, raw37610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37610step0 = (fun i j => raw37610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37610step0 raw37610; decide +kernel
      have hl : raw37610step0Labels = raw37610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37610 raw37610Labels permutation346 hz
    mixedMoment B raw37610step0 raw37610step0Labels = mixedMoment B raw37610step1 raw37610step1Labels := by
      have ha : raw37610step1 = (fun i j => raw37610step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37610step1 raw37610step0; decide +kernel
      have hl : raw37610step1Labels = raw37610step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37610step0 raw37610step0Labels permutation38 permutation4
    mixedMoment B raw37610step1 raw37610step1Labels = mixedMoment B raw37610step2 raw37610step2Labels := by
      have ha : raw37610step2 = -raw37610step1 := by apply Matrix.ext; change ∀ i j, raw37610step2 i j = -(raw37610step1 i j); unfold raw37610step2 raw37610step1; decide +kernel
      have hl : raw37610step2Labels = raw37610step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1590 node1590Labels := by rfl

def raw37611 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![-2, 0, 2], ![0, -3, 3]]
def raw37611step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-3, 0, 3]]
def raw37611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37611step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw37611step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37611 raw37611Labels = mixedMoment B node820 node820Labels := by
  calc
    mixedMoment B raw37611 raw37611Labels = mixedMoment B raw37611step0 raw37611step0Labels := by
      have hz : ∀ j, raw37611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37611step0 = (fun i j => raw37611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37611step0 raw37611; decide +kernel
      have hl : raw37611step0Labels = raw37611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37611 raw37611Labels permutation434 hz
    mixedMoment B raw37611step0 raw37611step0Labels = mixedMoment B raw37611step1 raw37611step1Labels := by
      have hz : ∀ j, raw37611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37611step1 = (fun i j => raw37611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37611step1 raw37611step0; decide +kernel
      have hl : raw37611step1Labels = raw37611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37611step0 raw37611step0Labels permutation80 hz
    mixedMoment B raw37611step1 raw37611step1Labels = mixedMoment B raw37611step2 raw37611step2Labels := by
      have ha : raw37611step2 = (fun i j => raw37611step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37611step2 raw37611step1; decide +kernel
      have hl : raw37611step2Labels = raw37611step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37611step1 raw37611step1Labels permutation10 permutation4
    mixedMoment B raw37611step2 raw37611step2Labels = mixedMoment B raw37611step3 raw37611step3Labels := by
      have ha : raw37611step3 = -raw37611step2 := by apply Matrix.ext; change ∀ i j, raw37611step3 i j = -(raw37611step2 i j); unfold raw37611step3 raw37611step2; decide +kernel
      have hl : raw37611step3Labels = raw37611step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node820 node820Labels := by rfl

def raw37612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw37612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw37612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37612 raw37612Labels = mixedMoment B node755 node755Labels := by
  calc
    mixedMoment B raw37612 raw37612Labels = mixedMoment B raw37612step0 raw37612step0Labels := by
      have hz : ∀ j, raw37612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37612step0 = (fun i j => raw37612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37612step0 raw37612; decide +kernel
      have hl : raw37612step0Labels = raw37612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37612 raw37612Labels permutation434 hz
    mixedMoment B raw37612step0 raw37612step0Labels = mixedMoment B raw37612step1 raw37612step1Labels := by
      have ha : raw37612step1 = (fun i j => raw37612step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37612step1 raw37612step0; decide +kernel
      have hl : raw37612step1Labels = raw37612step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37612step0 raw37612step0Labels permutation34 permutation4
    mixedMoment B raw37612step1 raw37612step1Labels = mixedMoment B raw37612step2 raw37612step2Labels := by
      have ha : raw37612step2 = -raw37612step1 := by apply Matrix.ext; change ∀ i j, raw37612step2 i j = -(raw37612step1 i j); unfold raw37612step2 raw37612step1; decide +kernel
      have hl : raw37612step2Labels = raw37612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node755 node755Labels := by rfl

def raw37613 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw37613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw37613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37613 raw37613Labels = mixedMoment B node755 node755Labels := by
  calc
    mixedMoment B raw37613 raw37613Labels = mixedMoment B raw37613step0 raw37613step0Labels := by
      have hz : ∀ j, raw37613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37613step0 = (fun i j => raw37613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37613step0 raw37613; decide +kernel
      have hl : raw37613step0Labels = raw37613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37613 raw37613Labels permutation346 hz
    mixedMoment B raw37613step0 raw37613step0Labels = mixedMoment B raw37613step1 raw37613step1Labels := by
      have ha : raw37613step1 = (fun i j => raw37613step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37613step1 raw37613step0; decide +kernel
      have hl : raw37613step1Labels = raw37613step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37613step0 raw37613step0Labels permutation34 permutation4
    mixedMoment B raw37613step1 raw37613step1Labels = mixedMoment B raw37613step2 raw37613step2Labels := by
      have ha : raw37613step2 = -raw37613step1 := by apply Matrix.ext; change ∀ i j, raw37613step2 i j = -(raw37613step1 i j); unfold raw37613step2 raw37613step1; decide +kernel
      have hl : raw37613step2Labels = raw37613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node755 node755Labels := by rfl

def raw37614 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -4, 3]]
def raw37614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -4, 3]]
def raw37614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![-2, 0, 2], ![1, -4, 3]]
def raw37614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-4, 1, 3]]
def raw37614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37614step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![4, -1, -3]]
def raw37614step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37614 raw37614Labels = mixedMoment B node759 node759Labels := by
  calc
    mixedMoment B raw37614 raw37614Labels = mixedMoment B raw37614step0 raw37614step0Labels := by
      have hz : ∀ j, raw37614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37614step0 = (fun i j => raw37614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37614step0 raw37614; decide +kernel
      have hl : raw37614step0Labels = raw37614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37614 raw37614Labels permutation434 hz
    mixedMoment B raw37614step0 raw37614step0Labels = mixedMoment B raw37614step1 raw37614step1Labels := by
      have hz : ∀ j, raw37614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37614step1 = (fun i j => raw37614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37614step1 raw37614step0; decide +kernel
      have hl : raw37614step1Labels = raw37614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37614step0 raw37614step0Labels permutation80 hz
    mixedMoment B raw37614step1 raw37614step1Labels = mixedMoment B raw37614step2 raw37614step2Labels := by
      have ha : raw37614step2 = (fun i j => raw37614step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37614step2 raw37614step1; decide +kernel
      have hl : raw37614step2Labels = raw37614step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37614step1 raw37614step1Labels permutation8 permutation4
    mixedMoment B raw37614step2 raw37614step2Labels = mixedMoment B raw37614step3 raw37614step3Labels := by
      have ha : raw37614step3 = -raw37614step2 := by apply Matrix.ext; change ∀ i j, raw37614step3 i j = -(raw37614step2 i j); unfold raw37614step3 raw37614step2; decide +kernel
      have hl : raw37614step3Labels = raw37614step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node759 node759Labels := by rfl

def raw37615 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37615 raw37615Labels = mixedMoment B node760 node760Labels := by
  calc
    mixedMoment B raw37615 raw37615Labels = mixedMoment B raw37615step0 raw37615step0Labels := by
      have ha : raw37615step0 = (fun i j => raw37615 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37615step0 raw37615; decide +kernel
      have hl : raw37615step0Labels = raw37615Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37615 raw37615Labels permutation152 permutation4
    mixedMoment B raw37615step0 raw37615step0Labels = mixedMoment B raw37615step1 raw37615step1Labels := by
      have ha : raw37615step1 = -raw37615step0 := by apply Matrix.ext; change ∀ i j, raw37615step1 i j = -(raw37615step0 i j); unfold raw37615step1 raw37615step0; decide +kernel
      have hl : raw37615step1Labels = raw37615step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node760 node760Labels := by rfl

def raw37616 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37616 raw37616Labels = mixedMoment B node1566 node1566Labels := by
  calc
    mixedMoment B raw37616 raw37616Labels = mixedMoment B raw37616step0 raw37616step0Labels := by
      have ha : raw37616step0 = (fun i j => raw37616 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37616step0 raw37616; decide +kernel
      have hl : raw37616step0Labels = raw37616Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37616 raw37616Labels permutation152 permutation4
    mixedMoment B raw37616step0 raw37616step0Labels = mixedMoment B raw37616step1 raw37616step1Labels := by
      have ha : raw37616step1 = -raw37616step0 := by apply Matrix.ext; change ∀ i j, raw37616step1 i j = -(raw37616step0 i j); unfold raw37616step1 raw37616step0; decide +kernel
      have hl : raw37616step1Labels = raw37616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1566 node1566Labels := by rfl

def raw37617 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37617 raw37617Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw37617 raw37617Labels = mixedMoment B raw37617step0 raw37617step0Labels := by
      have hz : ∀ j, raw37617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37617step0 = (fun i j => raw37617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37617step0 raw37617; decide +kernel
      have hl : raw37617step0Labels = raw37617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37617 raw37617Labels permutation346 hz
    mixedMoment B raw37617step0 raw37617step0Labels = mixedMoment B raw37617step1 raw37617step1Labels := by
      have ha : raw37617step1 = (fun i j => raw37617step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37617step1 raw37617step0; decide +kernel
      have hl : raw37617step1Labels = raw37617step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37617step0 raw37617step0Labels permutation32 permutation4
    mixedMoment B raw37617step1 raw37617step1Labels = mixedMoment B raw37617step2 raw37617step2Labels := by
      have ha : raw37617step2 = -raw37617step1 := by apply Matrix.ext; change ∀ i j, raw37617step2 i j = -(raw37617step1 i j); unfold raw37617step2 raw37617step1; decide +kernel
      have hl : raw37617step2Labels = raw37617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1690 node1690Labels := by rfl

def raw37618 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37618 raw37618Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw37618 raw37618Labels = mixedMoment B raw37618step0 raw37618step0Labels := by
      have ha : raw37618step0 = (fun i j => raw37618 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37618step0 raw37618; decide +kernel
      have hl : raw37618step0Labels = raw37618Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37618 raw37618Labels permutation158 permutation4
    mixedMoment B raw37618step0 raw37618step0Labels = mixedMoment B raw37618step1 raw37618step1Labels := by
      have ha : raw37618step1 = -raw37618step0 := by apply Matrix.ext; change ∀ i j, raw37618step1 i j = -(raw37618step0 i j); unfold raw37618step1 raw37618step0; decide +kernel
      have hl : raw37618step1Labels = raw37618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw37619 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37619Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37619step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37619 raw37619Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw37619 raw37619Labels = mixedMoment B raw37619step0 raw37619step0Labels := by
      have ha : raw37619step0 = (fun i j => raw37619 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37619step0 raw37619; decide +kernel
      have hl : raw37619step0Labels = raw37619Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37619 raw37619Labels permutation164 permutation4
    mixedMoment B raw37619step0 raw37619step0Labels = mixedMoment B raw37619step1 raw37619step1Labels := by
      have ha : raw37619step1 = -raw37619step0 := by apply Matrix.ext; change ∀ i j, raw37619step1 i j = -(raw37619step0 i j); unfold raw37619step1 raw37619step0; decide +kernel
      have hl : raw37619step1Labels = raw37619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw37620 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37620step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37620 raw37620Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw37620 raw37620Labels = mixedMoment B raw37620step0 raw37620step0Labels := by
      have ha : raw37620step0 = (fun i j => raw37620 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37620step0 raw37620; decide +kernel
      have hl : raw37620step0Labels = raw37620Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37620 raw37620Labels permutation170 permutation4
    mixedMoment B raw37620step0 raw37620step0Labels = mixedMoment B raw37620step1 raw37620step1Labels := by
      have ha : raw37620step1 = -raw37620step0 := by apply Matrix.ext; change ∀ i j, raw37620step1 i j = -(raw37620step0 i j); unfold raw37620step1 raw37620step0; decide +kernel
      have hl : raw37620step1Labels = raw37620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1684 node1684Labels := by rfl

def raw37621 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37621Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37621step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37621step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37621step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw37621step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37621 raw37621Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw37621 raw37621Labels = mixedMoment B raw37621step0 raw37621step0Labels := by
      have hz : ∀ j, raw37621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37621step0 = (fun i j => raw37621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37621step0 raw37621; decide +kernel
      have hl : raw37621step0Labels = raw37621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37621 raw37621Labels permutation346 hz
    mixedMoment B raw37621step0 raw37621step0Labels = mixedMoment B raw37621step1 raw37621step1Labels := by
      have ha : raw37621step1 = -raw37621step0 := by apply Matrix.ext; change ∀ i j, raw37621step1 i j = -(raw37621step0 i j); unfold raw37621step1 raw37621step0; decide +kernel
      have hl : raw37621step1Labels = raw37621step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4064 node4064Labels := by rfl

def raw37622 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37622Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37622 raw37622Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw37622 raw37622Labels = mixedMoment B raw37622step0 raw37622step0Labels := by
      have hz : ∀ j, raw37622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37622step0 = (fun i j => raw37622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37622step0 raw37622; decide +kernel
      have hl : raw37622step0Labels = raw37622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37622 raw37622Labels permutation346 hz
    mixedMoment B raw37622step0 raw37622step0Labels = mixedMoment B raw37622step1 raw37622step1Labels := by
      have ha : raw37622step1 = -raw37622step0 := by apply Matrix.ext; change ∀ i j, raw37622step1 i j = -(raw37622step0 i j); unfold raw37622step1 raw37622step0; decide +kernel
      have hl : raw37622step1Labels = raw37622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1690 node1690Labels := by rfl

def raw37623 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37623 raw37623Labels = mixedMoment B node3273 node3273Labels := by
  calc
    mixedMoment B raw37623 raw37623Labels = mixedMoment B raw37623step0 raw37623step0Labels := by
      have hz : ∀ j, raw37623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37623step0 = (fun i j => raw37623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37623step0 raw37623; decide +kernel
      have hl : raw37623step0Labels = raw37623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37623 raw37623Labels permutation346 hz
    mixedMoment B raw37623step0 raw37623step0Labels = mixedMoment B raw37623step1 raw37623step1Labels := by
      have ha : raw37623step1 = -raw37623step0 := by apply Matrix.ext; change ∀ i j, raw37623step1 i j = -(raw37623step0 i j); unfold raw37623step1 raw37623step0; decide +kernel
      have hl : raw37623step1Labels = raw37623step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3273 node3273Labels := by rfl

def raw37624 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw37624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw37624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37624 raw37624Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw37624 raw37624Labels = mixedMoment B raw37624step0 raw37624step0Labels := by
      have ha : raw37624step0 = (fun i j => raw37624 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37624step0 raw37624; decide +kernel
      have hl : raw37624step0Labels = raw37624Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37624 raw37624Labels permutation160 permutation4
    mixedMoment B raw37624step0 raw37624step0Labels = mixedMoment B raw37624step1 raw37624step1Labels := by
      have ha : raw37624step1 = -raw37624step0 := by apply Matrix.ext; change ∀ i j, raw37624step1 i j = -(raw37624step0 i j); unfold raw37624step1 raw37624step0; decide +kernel
      have hl : raw37624step1Labels = raw37624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3255 node3255Labels := by rfl

def raw37625 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37625 raw37625Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw37625 raw37625Labels = mixedMoment B raw37625step0 raw37625step0Labels := by
      have hz : ∀ j, raw37625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37625step0 = (fun i j => raw37625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37625step0 raw37625; decide +kernel
      have hl : raw37625step0Labels = raw37625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37625 raw37625Labels permutation346 hz
    mixedMoment B raw37625step0 raw37625step0Labels = mixedMoment B raw37625step1 raw37625step1Labels := by
      have ha : raw37625step1 = (fun i j => raw37625step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37625step1 raw37625step0; decide +kernel
      have hl : raw37625step1Labels = raw37625step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37625step0 raw37625step0Labels permutation34 permutation4
    mixedMoment B raw37625step1 raw37625step1Labels = mixedMoment B raw37625step2 raw37625step2Labels := by
      have ha : raw37625step2 = -raw37625step1 := by apply Matrix.ext; change ∀ i j, raw37625step2 i j = -(raw37625step1 i j); unfold raw37625step2 raw37625step1; decide +kernel
      have hl : raw37625step2Labels = raw37625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3264 node3264Labels := by rfl

def raw37626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37626 raw37626Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw37626 raw37626Labels = mixedMoment B raw37626step0 raw37626step0Labels := by
      have hz : ∀ j, raw37626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37626step0 = (fun i j => raw37626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37626step0 raw37626; decide +kernel
      have hl : raw37626step0Labels = raw37626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37626 raw37626Labels permutation346 hz
    mixedMoment B raw37626step0 raw37626step0Labels = mixedMoment B raw37626step1 raw37626step1Labels := by
      have ha : raw37626step1 = (fun i j => raw37626step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37626step1 raw37626step0; decide +kernel
      have hl : raw37626step1Labels = raw37626step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37626step0 raw37626step0Labels permutation32 permutation4
    mixedMoment B raw37626step1 raw37626step1Labels = mixedMoment B raw37626step2 raw37626step2Labels := by
      have ha : raw37626step2 = -raw37626step1 := by apply Matrix.ext; change ∀ i j, raw37626step2 i j = -(raw37626step1 i j); unfold raw37626step2 raw37626step1; decide +kernel
      have hl : raw37626step2Labels = raw37626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3264 node3264Labels := by rfl

def raw37627 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37627 raw37627Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw37627 raw37627Labels = mixedMoment B raw37627step0 raw37627step0Labels := by
      have hz : ∀ j, raw37627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37627step0 = (fun i j => raw37627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37627step0 raw37627; decide +kernel
      have hl : raw37627step0Labels = raw37627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37627 raw37627Labels permutation346 hz
    mixedMoment B raw37627step0 raw37627step0Labels = mixedMoment B raw37627step1 raw37627step1Labels := by
      have ha : raw37627step1 = (fun i j => raw37627step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37627step1 raw37627step0; decide +kernel
      have hl : raw37627step1Labels = raw37627step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37627step0 raw37627step0Labels permutation145 permutation4
    _ = mixedMoment B node2184 node2184Labels := by rfl

def raw37628 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37628Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw37628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37628 raw37628Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw37628 raw37628Labels = mixedMoment B raw37628step0 raw37628step0Labels := by
      have hz : ∀ j, raw37628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37628step0 = (fun i j => raw37628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37628step0 raw37628; decide +kernel
      have hl : raw37628step0Labels = raw37628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37628 raw37628Labels permutation346 hz
    mixedMoment B raw37628step0 raw37628step0Labels = mixedMoment B raw37628step1 raw37628step1Labels := by
      have ha : raw37628step1 = (fun i j => raw37628step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37628step1 raw37628step0; decide +kernel
      have hl : raw37628step1Labels = raw37628step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37628step0 raw37628step0Labels permutation32 permutation4
    mixedMoment B raw37628step1 raw37628step1Labels = mixedMoment B raw37628step2 raw37628step2Labels := by
      have ha : raw37628step2 = -raw37628step1 := by apply Matrix.ext; change ∀ i j, raw37628step2 i j = -(raw37628step1 i j); unfold raw37628step2 raw37628step1; decide +kernel
      have hl : raw37628step2Labels = raw37628step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw37629 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw37629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw37629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37629 raw37629Labels = mixedMoment B node1550 node1550Labels := by
  calc
    mixedMoment B raw37629 raw37629Labels = mixedMoment B raw37629step0 raw37629step0Labels := by
      have ha : raw37629step0 = (fun i j => raw37629 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37629step0 raw37629; decide +kernel
      have hl : raw37629step0Labels = raw37629Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37629 raw37629Labels permutation160 permutation4
    mixedMoment B raw37629step0 raw37629step0Labels = mixedMoment B raw37629step1 raw37629step1Labels := by
      have ha : raw37629step1 = -raw37629step0 := by apply Matrix.ext; change ∀ i j, raw37629step1 i j = -(raw37629step0 i j); unfold raw37629step1 raw37629step0; decide +kernel
      have hl : raw37629step1Labels = raw37629step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1550 node1550Labels := by rfl

def raw37630 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw37630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw37630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37630 raw37630Labels = mixedMoment B node1557 node1557Labels := by
  calc
    mixedMoment B raw37630 raw37630Labels = mixedMoment B raw37630step0 raw37630step0Labels := by
      have hz : ∀ j, raw37630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37630step0 = (fun i j => raw37630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37630step0 raw37630; decide +kernel
      have hl : raw37630step0Labels = raw37630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37630 raw37630Labels permutation346 hz
    mixedMoment B raw37630step0 raw37630step0Labels = mixedMoment B raw37630step1 raw37630step1Labels := by
      have ha : raw37630step1 = (fun i j => raw37630step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37630step1 raw37630step0; decide +kernel
      have hl : raw37630step1Labels = raw37630step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37630step0 raw37630step0Labels permutation34 permutation4
    mixedMoment B raw37630step1 raw37630step1Labels = mixedMoment B raw37630step2 raw37630step2Labels := by
      have ha : raw37630step2 = -raw37630step1 := by apply Matrix.ext; change ∀ i j, raw37630step2 i j = -(raw37630step1 i j); unfold raw37630step2 raw37630step1; decide +kernel
      have hl : raw37630step2Labels = raw37630step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1557 node1557Labels := by rfl

def raw37631 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -3, 3]]
def raw37631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -3, 3]]
def raw37631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw37631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw37631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37631 raw37631Labels = mixedMoment B node1557 node1557Labels := by
  calc
    mixedMoment B raw37631 raw37631Labels = mixedMoment B raw37631step0 raw37631step0Labels := by
      have hz : ∀ j, raw37631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37631step0 = (fun i j => raw37631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37631step0 raw37631; decide +kernel
      have hl : raw37631step0Labels = raw37631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37631 raw37631Labels permutation346 hz
    mixedMoment B raw37631step0 raw37631step0Labels = mixedMoment B raw37631step1 raw37631step1Labels := by
      have ha : raw37631step1 = (fun i j => raw37631step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37631step1 raw37631step0; decide +kernel
      have hl : raw37631step1Labels = raw37631step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37631step0 raw37631step0Labels permutation32 permutation4
    mixedMoment B raw37631step1 raw37631step1Labels = mixedMoment B raw37631step2 raw37631step2Labels := by
      have ha : raw37631step2 = -raw37631step1 := by apply Matrix.ext; change ∀ i j, raw37631step2 i j = -(raw37631step1 i j); unfold raw37631step2 raw37631step1; decide +kernel
      have hl : raw37631step2Labels = raw37631step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1557 node1557Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
