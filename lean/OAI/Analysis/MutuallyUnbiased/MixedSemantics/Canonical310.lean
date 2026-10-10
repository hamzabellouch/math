import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.ExtraNodes

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39680Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39680step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw39680step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39680step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39680 raw39680Labels = mixedMoment B node487 node487Labels := by
  calc
    mixedMoment B raw39680 raw39680Labels = mixedMoment B raw39680step0 raw39680step0Labels := by
      have hz : ∀ j, raw39680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39680step0 = (fun i j => raw39680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39680step0 raw39680; decide +kernel
      have hl : raw39680step0Labels = raw39680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39680 raw39680Labels permutation434 hz
    mixedMoment B raw39680step0 raw39680step0Labels = mixedMoment B raw39680step1 raw39680step1Labels := by
      have ha : raw39680step1 = (fun i j => raw39680step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39680step1 raw39680step0; decide +kernel
      have hl : raw39680step1Labels = raw39680step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39680step0 raw39680step0Labels permutation151 permutation3
    mixedMoment B raw39680step1 raw39680step1Labels = mixedMoment B raw39680step2 raw39680step2Labels := by
      have ha : raw39680step2 = -raw39680step1 := by apply Matrix.ext; change ∀ i j, raw39680step2 i j = -(raw39680step1 i j); unfold raw39680step2 raw39680step1; decide +kernel
      have hl : raw39680step2Labels = raw39680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node487 node487Labels := by rfl

def raw39681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39681Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39681step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39681step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39681step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39681 raw39681Labels = mixedMoment B node491 node491Labels := by
  calc
    mixedMoment B raw39681 raw39681Labels = mixedMoment B raw39681step0 raw39681step0Labels := by
      have hz : ∀ j, raw39681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39681step0 = (fun i j => raw39681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39681step0 raw39681; decide +kernel
      have hl : raw39681step0Labels = raw39681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39681 raw39681Labels permutation434 hz
    mixedMoment B raw39681step0 raw39681step0Labels = mixedMoment B raw39681step1 raw39681step1Labels := by
      have ha : raw39681step1 = (fun i j => raw39681step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39681step1 raw39681step0; decide +kernel
      have hl : raw39681step1Labels = raw39681step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39681step0 raw39681step0Labels permutation42 permutation5
    mixedMoment B raw39681step1 raw39681step1Labels = mixedMoment B raw39681step2 raw39681step2Labels := by
      have ha : raw39681step2 = -raw39681step1 := by apply Matrix.ext; change ∀ i j, raw39681step2 i j = -(raw39681step1 i j); unfold raw39681step2 raw39681step1; decide +kernel
      have hl : raw39681step2Labels = raw39681step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node491 node491Labels := by rfl

def raw39682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39682Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39682step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39682step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39682 raw39682Labels = mixedMoment B node484 node484Labels := by
  calc
    mixedMoment B raw39682 raw39682Labels = mixedMoment B raw39682step0 raw39682step0Labels := by
      have ha : raw39682step0 = (fun i j => raw39682 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39682step0 raw39682; decide +kernel
      have hl : raw39682step0Labels = raw39682Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39682 raw39682Labels permutation184 permutation5
    mixedMoment B raw39682step0 raw39682step0Labels = mixedMoment B raw39682step1 raw39682step1Labels := by
      have ha : raw39682step1 = -raw39682step0 := by apply Matrix.ext; change ∀ i j, raw39682step1 i j = -(raw39682step0 i j); unfold raw39682step1 raw39682step0; decide +kernel
      have hl : raw39682step1Labels = raw39682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node484 node484Labels := by rfl

def raw39683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39683Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39683step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39683step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39683 raw39683Labels = mixedMoment B node486 node486Labels := by
  calc
    mixedMoment B raw39683 raw39683Labels = mixedMoment B raw39683step0 raw39683step0Labels := by
      have ha : raw39683step0 = (fun i j => raw39683 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39683step0 raw39683; decide +kernel
      have hl : raw39683step0Labels = raw39683Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39683 raw39683Labels permutation182 permutation5
    mixedMoment B raw39683step0 raw39683step0Labels = mixedMoment B raw39683step1 raw39683step1Labels := by
      have ha : raw39683step1 = -raw39683step0 := by apply Matrix.ext; change ∀ i j, raw39683step1 i j = -(raw39683step0 i j); unfold raw39683step1 raw39683step0; decide +kernel
      have hl : raw39683step1Labels = raw39683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node486 node486Labels := by rfl

def raw39684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39684Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39684step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39684step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39684step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39684 raw39684Labels = mixedMoment B node501 node501Labels := by
  calc
    mixedMoment B raw39684 raw39684Labels = mixedMoment B raw39684step0 raw39684step0Labels := by
      have hz : ∀ j, raw39684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39684step0 = (fun i j => raw39684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39684step0 raw39684; decide +kernel
      have hl : raw39684step0Labels = raw39684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39684 raw39684Labels permutation434 hz
    mixedMoment B raw39684step0 raw39684step0Labels = mixedMoment B raw39684step1 raw39684step1Labels := by
      have hz : ∀ j, raw39684step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39684step1 = (fun i j => raw39684step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39684step1 raw39684step0; decide +kernel
      have hl : raw39684step1Labels = raw39684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39684step0 raw39684step0Labels permutation80 hz
    mixedMoment B raw39684step1 raw39684step1Labels = mixedMoment B raw39684step2 raw39684step2Labels := by
      have ha : raw39684step2 = (fun i j => raw39684step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39684step2 raw39684step1; decide +kernel
      have hl : raw39684step2Labels = raw39684step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39684step1 raw39684step1Labels permutation8 permutation3
    _ = mixedMoment B node501 node501Labels := by rfl

def raw39685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39685Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39685step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39685step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw39685step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39685step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39685 raw39685Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39685 raw39685Labels = mixedMoment B raw39685step0 raw39685step0Labels := by
      have hz : ∀ j, raw39685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39685step0 = (fun i j => raw39685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39685step0 raw39685; decide +kernel
      have hl : raw39685step0Labels = raw39685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39685 raw39685Labels permutation434 hz
    mixedMoment B raw39685step0 raw39685step0Labels = mixedMoment B raw39685step1 raw39685step1Labels := by
      have hz : ∀ j, raw39685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39685step1 = (fun i j => raw39685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39685step1 raw39685step0; decide +kernel
      have hl : raw39685step1Labels = raw39685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39685step0 raw39685step0Labels permutation80 hz
    mixedMoment B raw39685step1 raw39685step1Labels = mixedMoment B raw39685step2 raw39685step2Labels := by
      have ha : raw39685step2 = (fun i j => raw39685step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39685step2 raw39685step1; decide +kernel
      have hl : raw39685step2Labels = raw39685step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39685step1 raw39685step1Labels permutation31 permutation2
    mixedMoment B raw39685step2 raw39685step2Labels = mixedMoment B raw39685step3 raw39685step3Labels := by
      have ha : raw39685step3 = -raw39685step2 := by apply Matrix.ext; change ∀ i j, raw39685step3 i j = -(raw39685step2 i j); unfold raw39685step3 raw39685step2; decide +kernel
      have hl : raw39685step3Labels = raw39685step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

def raw39686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39686Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39686step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39686step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39686step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39686 raw39686Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39686 raw39686Labels = mixedMoment B raw39686step0 raw39686step0Labels := by
      have hz : ∀ j, raw39686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39686step0 = (fun i j => raw39686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39686step0 raw39686; decide +kernel
      have hl : raw39686step0Labels = raw39686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39686 raw39686Labels permutation434 hz
    mixedMoment B raw39686step0 raw39686step0Labels = mixedMoment B raw39686step1 raw39686step1Labels := by
      have hz : ∀ j, raw39686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39686step1 = (fun i j => raw39686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39686step1 raw39686step0; decide +kernel
      have hl : raw39686step1Labels = raw39686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39686step0 raw39686step0Labels permutation80 hz
    mixedMoment B raw39686step1 raw39686step1Labels = mixedMoment B raw39686step2 raw39686step2Labels := by
      have ha : raw39686step2 = (fun i j => raw39686step1 (permutation27 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39686step2 raw39686step1; decide +kernel
      have hl : raw39686step2Labels = raw39686step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39686step1 raw39686step1Labels permutation27 permutation7
    _ = mixedMoment B node410 node410Labels := by rfl

def raw39687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39687Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39687step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39687step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39687step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39687 raw39687Labels = mixedMoment B node498 node498Labels := by
  calc
    mixedMoment B raw39687 raw39687Labels = mixedMoment B raw39687step0 raw39687step0Labels := by
      have hz : ∀ j, raw39687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39687step0 = (fun i j => raw39687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39687step0 raw39687; decide +kernel
      have hl : raw39687step0Labels = raw39687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39687 raw39687Labels permutation346 hz
    mixedMoment B raw39687step0 raw39687step0Labels = mixedMoment B raw39687step1 raw39687step1Labels := by
      have ha : raw39687step1 = (fun i j => raw39687step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39687step1 raw39687step0; decide +kernel
      have hl : raw39687step1Labels = raw39687step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39687step0 raw39687step0Labels permutation40 permutation5
    mixedMoment B raw39687step1 raw39687step1Labels = mixedMoment B raw39687step2 raw39687step2Labels := by
      have ha : raw39687step2 = -raw39687step1 := by apply Matrix.ext; change ∀ i j, raw39687step2 i j = -(raw39687step1 i j); unfold raw39687step2 raw39687step1; decide +kernel
      have hl : raw39687step2Labels = raw39687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node498 node498Labels := by rfl

def raw39688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39688Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39688step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39688step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39688 raw39688Labels = mixedMoment B node500 node500Labels := by
  calc
    mixedMoment B raw39688 raw39688Labels = mixedMoment B raw39688step0 raw39688step0Labels := by
      have hz : ∀ j, raw39688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39688step0 = (fun i j => raw39688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39688step0 raw39688; decide +kernel
      have hl : raw39688step0Labels = raw39688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39688 raw39688Labels permutation346 hz
    mixedMoment B raw39688step0 raw39688step0Labels = mixedMoment B raw39688step1 raw39688step1Labels := by
      have ha : raw39688step1 = (fun i j => raw39688step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39688step1 raw39688step0; decide +kernel
      have hl : raw39688step1Labels = raw39688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39688step0 raw39688step0Labels permutation32 permutation3
    _ = mixedMoment B node500 node500Labels := by rfl

def raw39689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39689Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39689step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39689step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39689step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39689 raw39689Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39689 raw39689Labels = mixedMoment B raw39689step0 raw39689step0Labels := by
      have hz : ∀ j, raw39689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39689step0 = (fun i j => raw39689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39689step0 raw39689; decide +kernel
      have hl : raw39689step0Labels = raw39689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39689 raw39689Labels permutation434 hz
    mixedMoment B raw39689step0 raw39689step0Labels = mixedMoment B raw39689step1 raw39689step1Labels := by
      have ha : raw39689step1 = (fun i j => raw39689step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39689step1 raw39689step0; decide +kernel
      have hl : raw39689step1Labels = raw39689step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39689step0 raw39689step0Labels permutation68 permutation6
    mixedMoment B raw39689step1 raw39689step1Labels = mixedMoment B raw39689step2 raw39689step2Labels := by
      have ha : raw39689step2 = -raw39689step1 := by apply Matrix.ext; change ∀ i j, raw39689step2 i j = -(raw39689step1 i j); unfold raw39689step2 raw39689step1; decide +kernel
      have hl : raw39689step2Labels = raw39689step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node384 node384Labels := by rfl

def raw39690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39690Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39690step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw39690step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw39690step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw39690step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39690 raw39690Labels = mixedMoment B node385 node385Labels := by
  calc
    mixedMoment B raw39690 raw39690Labels = mixedMoment B raw39690step0 raw39690step0Labels := by
      have hz : ∀ j, raw39690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39690step0 = (fun i j => raw39690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39690step0 raw39690; decide +kernel
      have hl : raw39690step0Labels = raw39690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39690 raw39690Labels permutation434 hz
    mixedMoment B raw39690step0 raw39690step0Labels = mixedMoment B raw39690step1 raw39690step1Labels := by
      have hz : ∀ j, raw39690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39690step1 = (fun i j => raw39690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39690step1 raw39690step0; decide +kernel
      have hl : raw39690step1Labels = raw39690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39690step0 raw39690step0Labels permutation80 hz
    mixedMoment B raw39690step1 raw39690step1Labels = mixedMoment B raw39690step2 raw39690step2Labels := by
      have ha : raw39690step2 = (fun i j => raw39690step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39690step2 raw39690step1; decide +kernel
      have hl : raw39690step2Labels = raw39690step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39690step1 raw39690step1Labels permutation16 permutation6
    mixedMoment B raw39690step2 raw39690step2Labels = mixedMoment B raw39690step3 raw39690step3Labels := by
      have ha : raw39690step3 = -raw39690step2 := by apply Matrix.ext; change ∀ i j, raw39690step3 i j = -(raw39690step2 i j); unfold raw39690step3 raw39690step2; decide +kernel
      have hl : raw39690step3Labels = raw39690step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node385 node385Labels := by rfl

def raw39691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39691Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39691step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39691step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39691step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39691 raw39691Labels = mixedMoment B node495 node495Labels := by
  calc
    mixedMoment B raw39691 raw39691Labels = mixedMoment B raw39691step0 raw39691step0Labels := by
      have hz : ∀ j, raw39691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39691step0 = (fun i j => raw39691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39691step0 raw39691; decide +kernel
      have hl : raw39691step0Labels = raw39691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39691 raw39691Labels permutation434 hz
    mixedMoment B raw39691step0 raw39691step0Labels = mixedMoment B raw39691step1 raw39691step1Labels := by
      have hz : ∀ j, raw39691step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39691step1 = (fun i j => raw39691step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39691step1 raw39691step0; decide +kernel
      have hl : raw39691step1Labels = raw39691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39691step0 raw39691step0Labels permutation80 hz
    mixedMoment B raw39691step1 raw39691step1Labels = mixedMoment B raw39691step2 raw39691step2Labels := by
      have ha : raw39691step2 = (fun i j => raw39691step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39691step2 raw39691step1; decide +kernel
      have hl : raw39691step2Labels = raw39691step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39691step1 raw39691step1Labels permutation31 permutation5
    _ = mixedMoment B node495 node495Labels := by rfl

def raw39692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw39692Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw39692step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39692step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39692step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39692 raw39692Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw39692 raw39692Labels = mixedMoment B raw39692step0 raw39692step0Labels := by
      have hz : ∀ j, raw39692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39692step0 = (fun i j => raw39692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39692step0 raw39692; decide +kernel
      have hl : raw39692step0Labels = raw39692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39692 raw39692Labels permutation434 hz
    mixedMoment B raw39692step0 raw39692step0Labels = mixedMoment B raw39692step1 raw39692step1Labels := by
      have hz : ∀ j, raw39692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39692step1 = (fun i j => raw39692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39692step1 raw39692step0; decide +kernel
      have hl : raw39692step1Labels = raw39692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39692step0 raw39692step0Labels permutation80 hz
    mixedMoment B raw39692step1 raw39692step1Labels = mixedMoment B raw39692step2 raw39692step2Labels := by
      have ha : raw39692step2 = (fun i j => raw39692step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39692step2 raw39692step1; decide +kernel
      have hl : raw39692step2Labels = raw39692step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39692step1 raw39692step1Labels permutation31 permutation4
    _ = mixedMoment B node405 node405Labels := by rfl

def raw39693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39693Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39693step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39693step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw39693step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39693step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39693 raw39693Labels = mixedMoment B node5505 node5505Labels := by
  calc
    mixedMoment B raw39693 raw39693Labels = mixedMoment B raw39693step0 raw39693step0Labels := by
      have hz : ∀ j, raw39693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39693step0 = (fun i j => raw39693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39693step0 raw39693; decide +kernel
      have hl : raw39693step0Labels = raw39693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39693 raw39693Labels permutation434 hz
    mixedMoment B raw39693step0 raw39693step0Labels = mixedMoment B raw39693step1 raw39693step1Labels := by
      have hz : ∀ j, raw39693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39693step1 = (fun i j => raw39693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39693step1 raw39693step0; decide +kernel
      have hl : raw39693step1Labels = raw39693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39693step0 raw39693step0Labels permutation80 hz
    mixedMoment B raw39693step1 raw39693step1Labels = mixedMoment B raw39693step2 raw39693step2Labels := by
      have ha : raw39693step2 = (fun i j => raw39693step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39693step2 raw39693step1; decide +kernel
      have hl : raw39693step2Labels = raw39693step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39693step1 raw39693step1Labels permutation8 permutation5
    mixedMoment B raw39693step2 raw39693step2Labels = mixedMoment B raw39693step3 raw39693step3Labels := by
      have ha : raw39693step3 = -raw39693step2 := by apply Matrix.ext; change ∀ i j, raw39693step3 i j = -(raw39693step2 i j); unfold raw39693step3 raw39693step2; decide +kernel
      have hl : raw39693step3Labels = raw39693step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5505 node5505Labels := by rfl

def raw39694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39694Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39694step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39694step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39694 raw39694Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw39694 raw39694Labels = mixedMoment B raw39694step0 raw39694step0Labels := by
      have hz : ∀ j, raw39694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39694step0 = (fun i j => raw39694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39694step0 raw39694; decide +kernel
      have hl : raw39694step0Labels = raw39694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39694 raw39694Labels permutation346 hz
    mixedMoment B raw39694step0 raw39694step0Labels = mixedMoment B raw39694step1 raw39694step1Labels := by
      have ha : raw39694step1 = (fun i j => raw39694step0 (permutation121 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39694step1 raw39694step0; decide +kernel
      have hl : raw39694step1Labels = raw39694step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39694step0 raw39694step0Labels permutation121 permutation4
    _ = mixedMoment B node468 node468Labels := by rfl

def raw39695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39695Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39695step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39695step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39695step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39695 raw39695Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw39695 raw39695Labels = mixedMoment B raw39695step0 raw39695step0Labels := by
      have hz : ∀ j, raw39695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39695step0 = (fun i j => raw39695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39695step0 raw39695; decide +kernel
      have hl : raw39695step0Labels = raw39695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39695 raw39695Labels permutation346 hz
    mixedMoment B raw39695step0 raw39695step0Labels = mixedMoment B raw39695step1 raw39695step1Labels := by
      have ha : raw39695step1 = (fun i j => raw39695step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39695step1 raw39695step0; decide +kernel
      have hl : raw39695step1Labels = raw39695step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39695step0 raw39695step0Labels permutation34 permutation5
    mixedMoment B raw39695step1 raw39695step1Labels = mixedMoment B raw39695step2 raw39695step2Labels := by
      have ha : raw39695step2 = -raw39695step1 := by apply Matrix.ext; change ∀ i j, raw39695step2 i j = -(raw39695step1 i j); unfold raw39695step2 raw39695step1; decide +kernel
      have hl : raw39695step2Labels = raw39695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node489 node489Labels := by rfl

def raw39696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39696Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39696step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39696step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39696 raw39696Labels = mixedMoment B node490 node490Labels := by
  calc
    mixedMoment B raw39696 raw39696Labels = mixedMoment B raw39696step0 raw39696step0Labels := by
      have hz : ∀ j, raw39696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39696step0 = (fun i j => raw39696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39696step0 raw39696; decide +kernel
      have hl : raw39696step0Labels = raw39696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39696 raw39696Labels permutation346 hz
    mixedMoment B raw39696step0 raw39696step0Labels = mixedMoment B raw39696step1 raw39696step1Labels := by
      have ha : raw39696step1 = (fun i j => raw39696step0 (permutation103 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39696step1 raw39696step0; decide +kernel
      have hl : raw39696step1Labels = raw39696step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39696step0 raw39696step0Labels permutation103 permutation4
    _ = mixedMoment B node490 node490Labels := by rfl

def raw39697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39697Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39697step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39697step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39697 raw39697Labels = mixedMoment B node261 node261Labels := by
  calc
    mixedMoment B raw39697 raw39697Labels = mixedMoment B raw39697step0 raw39697step0Labels := by
      have hz : ∀ j, raw39697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39697step0 = (fun i j => raw39697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39697step0 raw39697; decide +kernel
      have hl : raw39697step0Labels = raw39697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39697 raw39697Labels permutation346 hz
    mixedMoment B raw39697step0 raw39697step0Labels = mixedMoment B raw39697step1 raw39697step1Labels := by
      have ha : raw39697step1 = (fun i j => raw39697step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39697step1 raw39697step0; decide +kernel
      have hl : raw39697step1Labels = raw39697step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39697step0 raw39697step0Labels permutation97 permutation4
    _ = mixedMoment B node261 node261Labels := by rfl

def raw39698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39698Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39698step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39698 raw39698Labels = mixedMoment B node462 node462Labels := by
  calc
    mixedMoment B raw39698 raw39698Labels = mixedMoment B raw39698step0 raw39698step0Labels := by
      have ha : raw39698step0 = (fun i j => raw39698 (permutation480 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39698step0 raw39698; decide +kernel
      have hl : raw39698step0Labels = raw39698Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39698 raw39698Labels permutation480 permutation4
    _ = mixedMoment B node462 node462Labels := by rfl

def raw39699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39699Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39699step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39699step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39699step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 2, 0], ![2, -2, 0]]
def raw39699step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw39699step4Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical39699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39699 raw39699Labels = mixedMoment B node6 node6Labels := by
  calc
    mixedMoment B raw39699 raw39699Labels = mixedMoment B raw39699step0 raw39699step0Labels := by
      have hz : ∀ j, raw39699 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39699step0 = (fun i j => raw39699 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39699step0 raw39699; decide +kernel
      have hl : raw39699step0Labels = raw39699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39699 raw39699Labels permutation520 hz
    mixedMoment B raw39699step0 raw39699step0Labels = mixedMoment B raw39699step1 raw39699step1Labels := by
      have hz : ∀ j, raw39699step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39699step1 = (fun i j => raw39699step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39699step1 raw39699step0; decide +kernel
      have hl : raw39699step1Labels = raw39699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39699step0 raw39699step0Labels permutation104 hz
    mixedMoment B raw39699step1 raw39699step1Labels = mixedMoment B raw39699step2 raw39699step2Labels := by
      have hz : ∀ j, raw39699step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39699step2 = (fun i j => raw39699step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39699step2 raw39699step1; decide +kernel
      have hl : raw39699step2Labels = raw39699step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39699step1 raw39699step1Labels permutation20 hz
    mixedMoment B raw39699step2 raw39699step2Labels = mixedMoment B raw39699step3 raw39699step3Labels := by
      have hz : ∀ j, raw39699step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw39699step3 = (fun i j => raw39699step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw39699step3 raw39699step2; decide +kernel
      have hl : raw39699step3Labels = raw39699step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39699step2 raw39699step2Labels permutation4 hz
    mixedMoment B raw39699step3 raw39699step3Labels = mixedMoment B raw39699step4 raw39699step4Labels := by
      have hz : ∀ i, raw39699step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39699step4 = (fun i j => raw39699step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39699step4 raw39699step3; decide +kernel
      have hl : raw39699step4Labels = (fun j => raw39699step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39699step3 raw39699step3Labels permutation6 hz
    _ = mixedMoment B node6 node6Labels := by rfl

def raw39700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39700Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39700step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39700step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39700step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39700step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39700step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw39700step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39700step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw39700step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39700 raw39700Labels = mixedMoment B node507 node507Labels := by
  calc
    mixedMoment B raw39700 raw39700Labels = mixedMoment B raw39700step0 raw39700step0Labels := by
      have hz : ∀ j, raw39700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39700step0 = (fun i j => raw39700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39700step0 raw39700; decide +kernel
      have hl : raw39700step0Labels = raw39700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39700 raw39700Labels permutation434 hz
    mixedMoment B raw39700step0 raw39700step0Labels = mixedMoment B raw39700step1 raw39700step1Labels := by
      have hz : ∀ j, raw39700step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39700step1 = (fun i j => raw39700step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39700step1 raw39700step0; decide +kernel
      have hl : raw39700step1Labels = raw39700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39700step0 raw39700step0Labels permutation80 hz
    mixedMoment B raw39700step1 raw39700step1Labels = mixedMoment B raw39700step2 raw39700step2Labels := by
      have hz : ∀ j, raw39700step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39700step2 = (fun i j => raw39700step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39700step2 raw39700step1; decide +kernel
      have hl : raw39700step2Labels = raw39700step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39700step1 raw39700step1Labels permutation14 hz
    mixedMoment B raw39700step2 raw39700step2Labels = mixedMoment B raw39700step3 raw39700step3Labels := by
      have ha : raw39700step3 = (fun i j => raw39700step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39700step3 raw39700step2; decide +kernel
      have hl : raw39700step3Labels = raw39700step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39700step2 raw39700step2Labels permutation7 permutation2
    mixedMoment B raw39700step3 raw39700step3Labels = mixedMoment B raw39700step4 raw39700step4Labels := by
      have ha : raw39700step4 = -raw39700step3 := by apply Matrix.ext; change ∀ i j, raw39700step4 i j = -(raw39700step3 i j); unfold raw39700step4 raw39700step3; decide +kernel
      have hl : raw39700step4Labels = raw39700step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node507 node507Labels := by rfl

def raw39701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39701Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39701step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39701step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39701step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39701step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39701step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39701step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39701 raw39701Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39701 raw39701Labels = mixedMoment B raw39701step0 raw39701step0Labels := by
      have hz : ∀ j, raw39701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39701step0 = (fun i j => raw39701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39701step0 raw39701; decide +kernel
      have hl : raw39701step0Labels = raw39701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39701 raw39701Labels permutation434 hz
    mixedMoment B raw39701step0 raw39701step0Labels = mixedMoment B raw39701step1 raw39701step1Labels := by
      have hz : ∀ j, raw39701step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39701step1 = (fun i j => raw39701step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39701step1 raw39701step0; decide +kernel
      have hl : raw39701step1Labels = raw39701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39701step0 raw39701step0Labels permutation80 hz
    mixedMoment B raw39701step1 raw39701step1Labels = mixedMoment B raw39701step2 raw39701step2Labels := by
      have hz : ∀ j, raw39701step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39701step2 = (fun i j => raw39701step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39701step2 raw39701step1; decide +kernel
      have hl : raw39701step2Labels = raw39701step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39701step1 raw39701step1Labels permutation14 hz
    mixedMoment B raw39701step2 raw39701step2Labels = mixedMoment B raw39701step3 raw39701step3Labels := by
      have ha : raw39701step3 = (fun i j => raw39701step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39701step3 raw39701step2; decide +kernel
      have hl : raw39701step3Labels = raw39701step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39701step2 raw39701step2Labels permutation7 permutation4
    _ = mixedMoment B node420 node420Labels := by rfl

def raw39702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39702Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39702step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39702step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39702step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39702step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39702step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw39702step3Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical39702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39702 raw39702Labels = mixedMoment B node5 node5Labels := by
  calc
    mixedMoment B raw39702 raw39702Labels = mixedMoment B raw39702step0 raw39702step0Labels := by
      have hz : ∀ j, raw39702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39702step0 = (fun i j => raw39702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39702step0 raw39702; decide +kernel
      have hl : raw39702step0Labels = raw39702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39702 raw39702Labels permutation434 hz
    mixedMoment B raw39702step0 raw39702step0Labels = mixedMoment B raw39702step1 raw39702step1Labels := by
      have hz : ∀ j, raw39702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39702step1 = (fun i j => raw39702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39702step1 raw39702step0; decide +kernel
      have hl : raw39702step1Labels = raw39702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39702step0 raw39702step0Labels permutation80 hz
    mixedMoment B raw39702step1 raw39702step1Labels = mixedMoment B raw39702step2 raw39702step2Labels := by
      have hz : ∀ j, raw39702step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39702step2 = (fun i j => raw39702step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39702step2 raw39702step1; decide +kernel
      have hl : raw39702step2Labels = raw39702step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39702step1 raw39702step1Labels permutation14 hz
    mixedMoment B raw39702step2 raw39702step2Labels = mixedMoment B raw39702step3 raw39702step3Labels := by
      have hz : ∀ i, raw39702step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39702step3 = (fun i j => raw39702step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39702step3 raw39702step2; decide +kernel
      have hl : raw39702step3Labels = (fun j => raw39702step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39702step2 raw39702step2Labels permutation6 hz
    _ = mixedMoment B node5 node5Labels := by rfl

def raw39703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39703Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39703step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39703step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39703step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39703 raw39703Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39703 raw39703Labels = mixedMoment B raw39703step0 raw39703step0Labels := by
      have hz : ∀ j, raw39703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39703step0 = (fun i j => raw39703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39703step0 raw39703; decide +kernel
      have hl : raw39703step0Labels = raw39703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39703 raw39703Labels permutation346 hz
    mixedMoment B raw39703step0 raw39703step0Labels = mixedMoment B raw39703step1 raw39703step1Labels := by
      have hz : ∀ j, raw39703step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39703step1 = (fun i j => raw39703step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39703step1 raw39703step0; decide +kernel
      have hl : raw39703step1Labels = raw39703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39703step0 raw39703step0Labels permutation56 hz
    mixedMoment B raw39703step1 raw39703step1Labels = mixedMoment B raw39703step2 raw39703step2Labels := by
      have ha : raw39703step2 = (fun i j => raw39703step1 (permutation26 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39703step2 raw39703step1; decide +kernel
      have hl : raw39703step2Labels = raw39703step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39703step1 raw39703step1Labels permutation26 permutation7
    _ = mixedMoment B node412 node412Labels := by rfl

def raw39704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39704Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39704step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39704step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39704step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39704step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39704 raw39704Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw39704 raw39704Labels = mixedMoment B raw39704step0 raw39704step0Labels := by
      have hz : ∀ j, raw39704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39704step0 = (fun i j => raw39704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39704step0 raw39704; decide +kernel
      have hl : raw39704step0Labels = raw39704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39704 raw39704Labels permutation346 hz
    mixedMoment B raw39704step0 raw39704step0Labels = mixedMoment B raw39704step1 raw39704step1Labels := by
      have hz : ∀ j, raw39704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39704step1 = (fun i j => raw39704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39704step1 raw39704step0; decide +kernel
      have hl : raw39704step1Labels = raw39704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39704step0 raw39704step0Labels permutation56 hz
    mixedMoment B raw39704step1 raw39704step1Labels = mixedMoment B raw39704step2 raw39704step2Labels := by
      have ha : raw39704step2 = (fun i j => raw39704step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39704step2 raw39704step1; decide +kernel
      have hl : raw39704step2Labels = raw39704step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39704step1 raw39704step1Labels permutation10 permutation5
    mixedMoment B raw39704step2 raw39704step2Labels = mixedMoment B raw39704step3 raw39704step3Labels := by
      have ha : raw39704step3 = -raw39704step2 := by apply Matrix.ext; change ∀ i j, raw39704step3 i j = -(raw39704step2 i j); unfold raw39704step3 raw39704step2; decide +kernel
      have hl : raw39704step3Labels = raw39704step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node503 node503Labels := by rfl

def raw39705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39705Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39705step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39705step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39705step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39705 raw39705Labels = mixedMoment B node506 node506Labels := by
  calc
    mixedMoment B raw39705 raw39705Labels = mixedMoment B raw39705step0 raw39705step0Labels := by
      have hz : ∀ j, raw39705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39705step0 = (fun i j => raw39705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39705step0 raw39705; decide +kernel
      have hl : raw39705step0Labels = raw39705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39705 raw39705Labels permutation346 hz
    mixedMoment B raw39705step0 raw39705step0Labels = mixedMoment B raw39705step1 raw39705step1Labels := by
      have hz : ∀ j, raw39705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39705step1 = (fun i j => raw39705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39705step1 raw39705step0; decide +kernel
      have hl : raw39705step1Labels = raw39705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39705step0 raw39705step0Labels permutation56 hz
    mixedMoment B raw39705step1 raw39705step1Labels = mixedMoment B raw39705step2 raw39705step2Labels := by
      have ha : raw39705step2 = (fun i j => raw39705step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39705step2 raw39705step1; decide +kernel
      have hl : raw39705step2Labels = raw39705step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39705step1 raw39705step1Labels permutation8 permutation3
    _ = mixedMoment B node506 node506Labels := by rfl

def raw39706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39706Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39706step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39706step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39706step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39706 raw39706Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39706 raw39706Labels = mixedMoment B raw39706step0 raw39706step0Labels := by
      have hz : ∀ j, raw39706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39706step0 = (fun i j => raw39706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39706step0 raw39706; decide +kernel
      have hl : raw39706step0Labels = raw39706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39706 raw39706Labels permutation346 hz
    mixedMoment B raw39706step0 raw39706step0Labels = mixedMoment B raw39706step1 raw39706step1Labels := by
      have hz : ∀ j, raw39706step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39706step1 = (fun i j => raw39706step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39706step1 raw39706step0; decide +kernel
      have hl : raw39706step1Labels = raw39706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39706step0 raw39706step0Labels permutation56 hz
    mixedMoment B raw39706step1 raw39706step1Labels = mixedMoment B raw39706step2 raw39706step2Labels := by
      have ha : raw39706step2 = (fun i j => raw39706step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39706step2 raw39706step1; decide +kernel
      have hl : raw39706step2Labels = raw39706step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39706step1 raw39706step1Labels permutation19 permutation4
    _ = mixedMoment B node496 node496Labels := by rfl

def raw39707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39707Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39707step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39707step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39707step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39707 raw39707Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39707 raw39707Labels = mixedMoment B raw39707step0 raw39707step0Labels := by
      have hz : ∀ j, raw39707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39707step0 = (fun i j => raw39707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39707step0 raw39707; decide +kernel
      have hl : raw39707step0Labels = raw39707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39707 raw39707Labels permutation346 hz
    mixedMoment B raw39707step0 raw39707step0Labels = mixedMoment B raw39707step1 raw39707step1Labels := by
      have hz : ∀ j, raw39707step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39707step1 = (fun i j => raw39707step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39707step1 raw39707step0; decide +kernel
      have hl : raw39707step1Labels = raw39707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39707step0 raw39707step0Labels permutation56 hz
    mixedMoment B raw39707step1 raw39707step1Labels = mixedMoment B raw39707step2 raw39707step2Labels := by
      have ha : raw39707step2 = (fun i j => raw39707step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39707step2 raw39707step1; decide +kernel
      have hl : raw39707step2Labels = raw39707step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39707step1 raw39707step1Labels permutation19 permutation4
    _ = mixedMoment B node268 node268Labels := by rfl

def raw39708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39708Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39708step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39708step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39708 raw39708Labels = mixedMoment B node504 node504Labels := by
  calc
    mixedMoment B raw39708 raw39708Labels = mixedMoment B raw39708step0 raw39708step0Labels := by
      have hz : ∀ j, raw39708 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39708step0 = (fun i j => raw39708 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39708step0 raw39708; decide +kernel
      have hl : raw39708step0Labels = raw39708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39708 raw39708Labels permutation265 hz
    mixedMoment B raw39708step0 raw39708step0Labels = mixedMoment B raw39708step1 raw39708step1Labels := by
      have ha : raw39708step1 = (fun i j => raw39708step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39708step1 raw39708step0; decide +kernel
      have hl : raw39708step1Labels = raw39708step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39708step0 raw39708step0Labels permutation32 permutation3
    _ = mixedMoment B node504 node504Labels := by rfl

def raw39709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39709Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39709step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39709step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39709 raw39709Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39709 raw39709Labels = mixedMoment B raw39709step0 raw39709step0Labels := by
      have hz : ∀ j, raw39709 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39709step0 = (fun i j => raw39709 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39709step0 raw39709; decide +kernel
      have hl : raw39709step0Labels = raw39709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39709 raw39709Labels permutation265 hz
    mixedMoment B raw39709step0 raw39709step0Labels = mixedMoment B raw39709step1 raw39709step1Labels := by
      have ha : raw39709step1 = (fun i j => raw39709step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39709step1 raw39709step0; decide +kernel
      have hl : raw39709step1Labels = raw39709step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39709step0 raw39709step0Labels permutation91 permutation4
    _ = mixedMoment B node467 node467Labels := by rfl

def raw39710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39710Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39710step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39710step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0]]
def raw39710step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw39710step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw39710step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39710 raw39710Labels = mixedMoment B node272 node272Labels := by
  calc
    mixedMoment B raw39710 raw39710Labels = mixedMoment B raw39710step0 raw39710step0Labels := by
      have hz : ∀ j, raw39710 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39710step0 = (fun i j => raw39710 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39710step0 raw39710; decide +kernel
      have hl : raw39710step0Labels = raw39710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39710 raw39710Labels permutation520 hz
    mixedMoment B raw39710step0 raw39710step0Labels = mixedMoment B raw39710step1 raw39710step1Labels := by
      have hz : ∀ j, raw39710step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39710step1 = (fun i j => raw39710step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39710step1 raw39710step0; decide +kernel
      have hl : raw39710step1Labels = raw39710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39710step0 raw39710step0Labels permutation104 hz
    mixedMoment B raw39710step1 raw39710step1Labels = mixedMoment B raw39710step2 raw39710step2Labels := by
      have hz : ∀ j, raw39710step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39710step2 = (fun i j => raw39710step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39710step2 raw39710step1; decide +kernel
      have hl : raw39710step2Labels = raw39710step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39710step1 raw39710step1Labels permutation20 hz
    mixedMoment B raw39710step2 raw39710step2Labels = mixedMoment B raw39710step3 raw39710step3Labels := by
      have ha : raw39710step3 = (fun i j => raw39710step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39710step3 raw39710step2; decide +kernel
      have hl : raw39710step3Labels = raw39710step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39710step2 raw39710step2Labels permutation7 permutation3
    mixedMoment B raw39710step3 raw39710step3Labels = mixedMoment B raw39710step4 raw39710step4Labels := by
      have ha : raw39710step4 = -raw39710step3 := by apply Matrix.ext; change ∀ i j, raw39710step4 i j = -(raw39710step3 i j); unfold raw39710step4 raw39710step3; decide +kernel
      have hl : raw39710step4Labels = raw39710step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node272 node272Labels := by rfl

def raw39711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39711Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39711step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39711step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39711step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39711step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39711 raw39711Labels = mixedMoment B node469 node469Labels := by
  calc
    mixedMoment B raw39711 raw39711Labels = mixedMoment B raw39711step0 raw39711step0Labels := by
      have hz : ∀ j, raw39711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39711step0 = (fun i j => raw39711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39711step0 raw39711; decide +kernel
      have hl : raw39711step0Labels = raw39711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39711 raw39711Labels permutation434 hz
    mixedMoment B raw39711step0 raw39711step0Labels = mixedMoment B raw39711step1 raw39711step1Labels := by
      have hz : ∀ j, raw39711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39711step1 = (fun i j => raw39711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39711step1 raw39711step0; decide +kernel
      have hl : raw39711step1Labels = raw39711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39711step0 raw39711step0Labels permutation80 hz
    mixedMoment B raw39711step1 raw39711step1Labels = mixedMoment B raw39711step2 raw39711step2Labels := by
      have ha : raw39711step2 = (fun i j => raw39711step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39711step2 raw39711step1; decide +kernel
      have hl : raw39711step2Labels = raw39711step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39711step1 raw39711step1Labels permutation31 permutation3
    mixedMoment B raw39711step2 raw39711step2Labels = mixedMoment B raw39711step3 raw39711step3Labels := by
      have ha : raw39711step3 = -raw39711step2 := by apply Matrix.ext; change ∀ i j, raw39711step3 i j = -(raw39711step2 i j); unfold raw39711step3 raw39711step2; decide +kernel
      have hl : raw39711step3Labels = raw39711step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node469 node469Labels := by rfl

def raw39712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39712Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39712step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39712step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw39712step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39712 raw39712Labels = mixedMoment B node516 node516Labels := by
  calc
    mixedMoment B raw39712 raw39712Labels = mixedMoment B raw39712step0 raw39712step0Labels := by
      have hz : ∀ j, raw39712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39712step0 = (fun i j => raw39712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39712step0 raw39712; decide +kernel
      have hl : raw39712step0Labels = raw39712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39712 raw39712Labels permutation434 hz
    mixedMoment B raw39712step0 raw39712step0Labels = mixedMoment B raw39712step1 raw39712step1Labels := by
      have hz : ∀ j, raw39712step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39712step1 = (fun i j => raw39712step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39712step1 raw39712step0; decide +kernel
      have hl : raw39712step1Labels = raw39712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39712step0 raw39712step0Labels permutation80 hz
    mixedMoment B raw39712step1 raw39712step1Labels = mixedMoment B raw39712step2 raw39712step2Labels := by
      have ha : raw39712step2 = (fun i j => raw39712step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39712step2 raw39712step1; decide +kernel
      have hl : raw39712step2Labels = raw39712step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39712step1 raw39712step1Labels permutation8 permutation3
    _ = mixedMoment B node516 node516Labels := by rfl

def raw39713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39713Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39713step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39713step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39713step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39713 raw39713Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39713 raw39713Labels = mixedMoment B raw39713step0 raw39713step0Labels := by
      have hz : ∀ j, raw39713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39713step0 = (fun i j => raw39713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39713step0 raw39713; decide +kernel
      have hl : raw39713step0Labels = raw39713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39713 raw39713Labels permutation434 hz
    mixedMoment B raw39713step0 raw39713step0Labels = mixedMoment B raw39713step1 raw39713step1Labels := by
      have hz : ∀ j, raw39713step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39713step1 = (fun i j => raw39713step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39713step1 raw39713step0; decide +kernel
      have hl : raw39713step1Labels = raw39713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39713step0 raw39713step0Labels permutation80 hz
    mixedMoment B raw39713step1 raw39713step1Labels = mixedMoment B raw39713step2 raw39713step2Labels := by
      have ha : raw39713step2 = (fun i j => raw39713step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39713step2 raw39713step1; decide +kernel
      have hl : raw39713step2Labels = raw39713step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39713step1 raw39713step1Labels permutation24 permutation4
    _ = mixedMoment B node410 node410Labels := by rfl

def raw39714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39714Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39714step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39714step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39714step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39714 raw39714Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw39714 raw39714Labels = mixedMoment B raw39714step0 raw39714step0Labels := by
      have hz : ∀ j, raw39714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39714step0 = (fun i j => raw39714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39714step0 raw39714; decide +kernel
      have hl : raw39714step0Labels = raw39714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39714 raw39714Labels permutation346 hz
    mixedMoment B raw39714step0 raw39714step0Labels = mixedMoment B raw39714step1 raw39714step1Labels := by
      have ha : raw39714step1 = (fun i j => raw39714step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39714step1 raw39714step0; decide +kernel
      have hl : raw39714step1Labels = raw39714step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39714step0 raw39714step0Labels permutation151 permutation3
    mixedMoment B raw39714step1 raw39714step1Labels = mixedMoment B raw39714step2 raw39714step2Labels := by
      have ha : raw39714step2 = -raw39714step1 := by apply Matrix.ext; change ∀ i j, raw39714step2 i j = -(raw39714step1 i j); unfold raw39714step2 raw39714step1; decide +kernel
      have hl : raw39714step2Labels = raw39714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node483 node483Labels := by rfl

def raw39715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39715Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39715step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39715step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39715step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39715 raw39715Labels = mixedMoment B node498 node498Labels := by
  calc
    mixedMoment B raw39715 raw39715Labels = mixedMoment B raw39715step0 raw39715step0Labels := by
      have hz : ∀ j, raw39715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39715step0 = (fun i j => raw39715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39715step0 raw39715; decide +kernel
      have hl : raw39715step0Labels = raw39715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39715 raw39715Labels permutation346 hz
    mixedMoment B raw39715step0 raw39715step0Labels = mixedMoment B raw39715step1 raw39715step1Labels := by
      have ha : raw39715step1 = (fun i j => raw39715step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39715step1 raw39715step0; decide +kernel
      have hl : raw39715step1Labels = raw39715step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39715step0 raw39715step0Labels permutation151 permutation2
    mixedMoment B raw39715step1 raw39715step1Labels = mixedMoment B raw39715step2 raw39715step2Labels := by
      have ha : raw39715step2 = -raw39715step1 := by apply Matrix.ext; change ∀ i j, raw39715step2 i j = -(raw39715step1 i j); unfold raw39715step2 raw39715step1; decide +kernel
      have hl : raw39715step2Labels = raw39715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node498 node498Labels := by rfl

def raw39716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39716Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39716step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39716step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39716step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39716 raw39716Labels = mixedMoment B node491 node491Labels := by
  calc
    mixedMoment B raw39716 raw39716Labels = mixedMoment B raw39716step0 raw39716step0Labels := by
      have hz : ∀ j, raw39716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39716step0 = (fun i j => raw39716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39716step0 raw39716; decide +kernel
      have hl : raw39716step0Labels = raw39716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39716 raw39716Labels permutation346 hz
    mixedMoment B raw39716step0 raw39716step0Labels = mixedMoment B raw39716step1 raw39716step1Labels := by
      have ha : raw39716step1 = (fun i j => raw39716step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39716step1 raw39716step0; decide +kernel
      have hl : raw39716step1Labels = raw39716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39716step0 raw39716step0Labels permutation151 permutation2
    mixedMoment B raw39716step1 raw39716step1Labels = mixedMoment B raw39716step2 raw39716step2Labels := by
      have ha : raw39716step2 = -raw39716step1 := by apply Matrix.ext; change ∀ i j, raw39716step2 i j = -(raw39716step1 i j); unfold raw39716step2 raw39716step1; decide +kernel
      have hl : raw39716step2Labels = raw39716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node491 node491Labels := by rfl

def raw39717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39717Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39717step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39717step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39717step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39717 raw39717Labels = mixedMoment B node514 node514Labels := by
  calc
    mixedMoment B raw39717 raw39717Labels = mixedMoment B raw39717step0 raw39717step0Labels := by
      have hz : ∀ j, raw39717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39717step0 = (fun i j => raw39717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39717step0 raw39717; decide +kernel
      have hl : raw39717step0Labels = raw39717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39717 raw39717Labels permutation346 hz
    mixedMoment B raw39717step0 raw39717step0Labels = mixedMoment B raw39717step1 raw39717step1Labels := by
      have ha : raw39717step1 = (fun i j => raw39717step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39717step1 raw39717step0; decide +kernel
      have hl : raw39717step1Labels = raw39717step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39717step0 raw39717step0Labels permutation56 permutation5
    mixedMoment B raw39717step1 raw39717step1Labels = mixedMoment B raw39717step2 raw39717step2Labels := by
      have ha : raw39717step2 = -raw39717step1 := by apply Matrix.ext; change ∀ i j, raw39717step2 i j = -(raw39717step1 i j); unfold raw39717step2 raw39717step1; decide +kernel
      have hl : raw39717step2Labels = raw39717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node514 node514Labels := by rfl

def raw39718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39718Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39718step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39718step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39718 raw39718Labels = mixedMoment B node515 node515Labels := by
  calc
    mixedMoment B raw39718 raw39718Labels = mixedMoment B raw39718step0 raw39718step0Labels := by
      have hz : ∀ j, raw39718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39718step0 = (fun i j => raw39718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39718step0 raw39718; decide +kernel
      have hl : raw39718step0Labels = raw39718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39718 raw39718Labels permutation346 hz
    mixedMoment B raw39718step0 raw39718step0Labels = mixedMoment B raw39718step1 raw39718step1Labels := by
      have ha : raw39718step1 = (fun i j => raw39718step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39718step1 raw39718step0; decide +kernel
      have hl : raw39718step1Labels = raw39718step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39718step0 raw39718step0Labels permutation32 permutation3
    _ = mixedMoment B node515 node515Labels := by rfl

def raw39719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39719Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39719step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39719step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39719 raw39719Labels = mixedMoment B node512 node512Labels := by
  calc
    mixedMoment B raw39719 raw39719Labels = mixedMoment B raw39719step0 raw39719step0Labels := by
      have ha : raw39719step0 = (fun i j => raw39719 (permutation273 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39719step0 raw39719; decide +kernel
      have hl : raw39719step0Labels = raw39719Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39719 raw39719Labels permutation273 permutation5
    mixedMoment B raw39719step0 raw39719step0Labels = mixedMoment B raw39719step1 raw39719step1Labels := by
      have ha : raw39719step1 = -raw39719step0 := by apply Matrix.ext; change ∀ i j, raw39719step1 i j = -(raw39719step0 i j); unfold raw39719step1 raw39719step0; decide +kernel
      have hl : raw39719step1Labels = raw39719step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node512 node512Labels := by rfl

def raw39720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39720Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39720step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39720 raw39720Labels = mixedMoment B node513 node513Labels := by
  calc
    mixedMoment B raw39720 raw39720Labels = mixedMoment B raw39720step0 raw39720step0Labels := by
      have ha : raw39720step0 = (fun i j => raw39720 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39720step0 raw39720; decide +kernel
      have hl : raw39720step0Labels = raw39720Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39720 raw39720Labels permutation152 permutation3
    _ = mixedMoment B node513 node513Labels := by rfl

def raw39721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39721Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39721step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39721step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw39721step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39721 raw39721Labels = mixedMoment B node5506 node5506Labels := by
  calc
    mixedMoment B raw39721 raw39721Labels = mixedMoment B raw39721step0 raw39721step0Labels := by
      have hz : ∀ j, raw39721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39721step0 = (fun i j => raw39721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39721step0 raw39721; decide +kernel
      have hl : raw39721step0Labels = raw39721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39721 raw39721Labels permutation434 hz
    mixedMoment B raw39721step0 raw39721step0Labels = mixedMoment B raw39721step1 raw39721step1Labels := by
      have hz : ∀ j, raw39721step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39721step1 = (fun i j => raw39721step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39721step1 raw39721step0; decide +kernel
      have hl : raw39721step1Labels = raw39721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39721step0 raw39721step0Labels permutation80 hz
    mixedMoment B raw39721step1 raw39721step1Labels = mixedMoment B raw39721step2 raw39721step2Labels := by
      have ha : raw39721step2 = (fun i j => raw39721step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39721step2 raw39721step1; decide +kernel
      have hl : raw39721step2Labels = raw39721step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39721step1 raw39721step1Labels permutation8 permutation3
    _ = mixedMoment B node5506 node5506Labels := by rfl

def raw39722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39722Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39722step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39722step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39722step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39722 raw39722Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw39722 raw39722Labels = mixedMoment B raw39722step0 raw39722step0Labels := by
      have hz : ∀ j, raw39722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39722step0 = (fun i j => raw39722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39722step0 raw39722; decide +kernel
      have hl : raw39722step0Labels = raw39722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39722 raw39722Labels permutation346 hz
    mixedMoment B raw39722step0 raw39722step0Labels = mixedMoment B raw39722step1 raw39722step1Labels := by
      have ha : raw39722step1 = (fun i j => raw39722step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39722step1 raw39722step0; decide +kernel
      have hl : raw39722step1Labels = raw39722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39722step0 raw39722step0Labels permutation151 permutation2
    mixedMoment B raw39722step1 raw39722step1Labels = mixedMoment B raw39722step2 raw39722step2Labels := by
      have ha : raw39722step2 = -raw39722step1 := by apply Matrix.ext; change ∀ i j, raw39722step2 i j = -(raw39722step1 i j); unfold raw39722step2 raw39722step1; decide +kernel
      have hl : raw39722step2Labels = raw39722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node489 node489Labels := by rfl

def raw39723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39723Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw39723step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw39723step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39723step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39723 raw39723Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39723 raw39723Labels = mixedMoment B raw39723step0 raw39723step0Labels := by
      have hz : ∀ j, raw39723 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39723step0 = (fun i j => raw39723 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39723step0 raw39723; decide +kernel
      have hl : raw39723step0Labels = raw39723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39723 raw39723Labels permutation520 hz
    mixedMoment B raw39723step0 raw39723step0Labels = mixedMoment B raw39723step1 raw39723step1Labels := by
      have hz : ∀ j, raw39723step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39723step1 = (fun i j => raw39723step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39723step1 raw39723step0; decide +kernel
      have hl : raw39723step1Labels = raw39723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39723step0 raw39723step0Labels permutation104 hz
    mixedMoment B raw39723step1 raw39723step1Labels = mixedMoment B raw39723step2 raw39723step2Labels := by
      have ha : raw39723step2 = (fun i j => raw39723step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39723step2 raw39723step1; decide +kernel
      have hl : raw39723step2Labels = raw39723step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39723step1 raw39723step1Labels permutation28 permutation5
    _ = mixedMoment B node268 node268Labels := by rfl

def raw39724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39724Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39724step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39724step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39724 raw39724Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39724 raw39724Labels = mixedMoment B raw39724step0 raw39724step0Labels := by
      have hz : ∀ j, raw39724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39724step0 = (fun i j => raw39724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39724step0 raw39724; decide +kernel
      have hl : raw39724step0Labels = raw39724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39724 raw39724Labels permutation434 hz
    mixedMoment B raw39724step0 raw39724step0Labels = mixedMoment B raw39724step1 raw39724step1Labels := by
      have ha : raw39724step1 = (fun i j => raw39724step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39724step1 raw39724step0; decide +kernel
      have hl : raw39724step1Labels = raw39724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39724step0 raw39724step0Labels permutation148 permutation5
    _ = mixedMoment B node467 node467Labels := by rfl

def raw39725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39725Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39725step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39725step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39725step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39725 raw39725Labels = mixedMoment B node498 node498Labels := by
  calc
    mixedMoment B raw39725 raw39725Labels = mixedMoment B raw39725step0 raw39725step0Labels := by
      have hz : ∀ j, raw39725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39725step0 = (fun i j => raw39725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39725step0 raw39725; decide +kernel
      have hl : raw39725step0Labels = raw39725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39725 raw39725Labels permutation434 hz
    mixedMoment B raw39725step0 raw39725step0Labels = mixedMoment B raw39725step1 raw39725step1Labels := by
      have ha : raw39725step1 = (fun i j => raw39725step0 (permutation81 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39725step1 raw39725step0; decide +kernel
      have hl : raw39725step1Labels = raw39725step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39725step0 raw39725step0Labels permutation81 permutation4
    mixedMoment B raw39725step1 raw39725step1Labels = mixedMoment B raw39725step2 raw39725step2Labels := by
      have ha : raw39725step2 = -raw39725step1 := by apply Matrix.ext; change ∀ i j, raw39725step2 i j = -(raw39725step1 i j); unfold raw39725step2 raw39725step1; decide +kernel
      have hl : raw39725step2Labels = raw39725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node498 node498Labels := by rfl

def raw39726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39726Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw39726step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39726step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39726 raw39726Labels = mixedMoment B node381 node381Labels := by
  calc
    mixedMoment B raw39726 raw39726Labels = mixedMoment B raw39726step0 raw39726step0Labels := by
      have hz : ∀ j, raw39726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39726step0 = (fun i j => raw39726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39726step0 raw39726; decide +kernel
      have hl : raw39726step0Labels = raw39726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39726 raw39726Labels permutation434 hz
    mixedMoment B raw39726step0 raw39726step0Labels = mixedMoment B raw39726step1 raw39726step1Labels := by
      have ha : raw39726step1 = (fun i j => raw39726step0 (permutation114 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39726step1 raw39726step0; decide +kernel
      have hl : raw39726step1Labels = raw39726step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39726step0 raw39726step0Labels permutation114 permutation4
    _ = mixedMoment B node381 node381Labels := by rfl

def raw39727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39727Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39727step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39727 raw39727Labels = mixedMoment B node480 node480Labels := by
  calc
    mixedMoment B raw39727 raw39727Labels = mixedMoment B raw39727step0 raw39727step0Labels := by
      have ha : raw39727step0 = (fun i j => raw39727 (permutation661 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39727step0 raw39727; decide +kernel
      have hl : raw39727step0Labels = raw39727Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39727 raw39727Labels permutation661 permutation5
    _ = mixedMoment B node480 node480Labels := by rfl

def raw39728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39728Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39728step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39728 raw39728Labels = mixedMoment B node444 node444Labels := by
  calc
    mixedMoment B raw39728 raw39728Labels = mixedMoment B raw39728step0 raw39728step0Labels := by
      have ha : raw39728step0 = (fun i j => raw39728 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39728step0 raw39728; decide +kernel
      have hl : raw39728step0Labels = raw39728Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39728 raw39728Labels permutation414 permutation6
    _ = mixedMoment B node444 node444Labels := by rfl

def raw39729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39729Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39729step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39729 raw39729Labels = mixedMoment B node443 node443Labels := by
  calc
    mixedMoment B raw39729 raw39729Labels = mixedMoment B raw39729step0 raw39729step0Labels := by
      have ha : raw39729step0 = (fun i j => raw39729 (permutation643 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39729step0 raw39729; decide +kernel
      have hl : raw39729step0Labels = raw39729Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39729 raw39729Labels permutation643 permutation7
    _ = mixedMoment B node443 node443Labels := by rfl

def raw39730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39730Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39730step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39730 raw39730Labels = mixedMoment B node485 node485Labels := by
  calc
    mixedMoment B raw39730 raw39730Labels = mixedMoment B raw39730step0 raw39730step0Labels := by
      have ha : raw39730step0 = (fun i j => raw39730 (permutation389 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39730step0 raw39730; decide +kernel
      have hl : raw39730step0Labels = raw39730Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39730 raw39730Labels permutation389 permutation6
    _ = mixedMoment B node485 node485Labels := by rfl

def raw39731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39731Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw39731step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39731step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39731 raw39731Labels = mixedMoment B node499 node499Labels := by
  calc
    mixedMoment B raw39731 raw39731Labels = mixedMoment B raw39731step0 raw39731step0Labels := by
      have ha : raw39731step0 = (fun i j => raw39731 (permutation346 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39731step0 raw39731; decide +kernel
      have hl : raw39731step0Labels = raw39731Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39731 raw39731Labels permutation346 permutation4
    mixedMoment B raw39731step0 raw39731step0Labels = mixedMoment B raw39731step1 raw39731step1Labels := by
      have ha : raw39731step1 = -raw39731step0 := by apply Matrix.ext; change ∀ i j, raw39731step1 i j = -(raw39731step0 i j); unfold raw39731step1 raw39731step0; decide +kernel
      have hl : raw39731step1Labels = raw39731step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node499 node499Labels := by rfl

def raw39732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39732Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39732step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39732 raw39732Labels = mixedMoment B node521 node521Labels := by
  calc
    mixedMoment B raw39732 raw39732Labels = mixedMoment B raw39732step0 raw39732step0Labels := by
      have hz : ∀ j, raw39732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39732step0 = (fun i j => raw39732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39732step0 raw39732; decide +kernel
      have hl : raw39732step0Labels = raw39732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39732 raw39732Labels permutation434 hz
    _ = mixedMoment B node521 node521Labels := by rfl

def raw39733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39733Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39733step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39733step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39733 raw39733Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw39733 raw39733Labels = mixedMoment B raw39733step0 raw39733step0Labels := by
      have ha : raw39733step0 = (fun i j => raw39733 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39733step0 raw39733; decide +kernel
      have hl : raw39733step0Labels = raw39733Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39733 raw39733Labels permutation682 permutation2
    mixedMoment B raw39733step0 raw39733step0Labels = mixedMoment B raw39733step1 raw39733step1Labels := by
      have ha : raw39733step1 = -raw39733step0 := by apply Matrix.ext; change ∀ i j, raw39733step1 i j = -(raw39733step0 i j); unfold raw39733step1 raw39733step0; decide +kernel
      have hl : raw39733step1Labels = raw39733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node479 node479Labels := by rfl

def raw39734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39734Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39734step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39734step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39734 raw39734Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39734 raw39734Labels = mixedMoment B raw39734step0 raw39734step0Labels := by
      have hz : ∀ j, raw39734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39734step0 = (fun i j => raw39734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39734step0 raw39734; decide +kernel
      have hl : raw39734step0Labels = raw39734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39734 raw39734Labels permutation346 hz
    mixedMoment B raw39734step0 raw39734step0Labels = mixedMoment B raw39734step1 raw39734step1Labels := by
      have ha : raw39734step1 = (fun i j => raw39734step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39734step1 raw39734step0; decide +kernel
      have hl : raw39734step1Labels = raw39734step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39734step0 raw39734step0Labels permutation122 permutation6
    _ = mixedMoment B node409 node409Labels := by rfl

def raw39735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39735Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39735step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39735step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39735 raw39735Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw39735 raw39735Labels = mixedMoment B raw39735step0 raw39735step0Labels := by
      have hz : ∀ j, raw39735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39735step0 = (fun i j => raw39735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39735step0 raw39735; decide +kernel
      have hl : raw39735step0Labels = raw39735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39735 raw39735Labels permutation346 hz
    mixedMoment B raw39735step0 raw39735step0Labels = mixedMoment B raw39735step1 raw39735step1Labels := by
      have ha : raw39735step1 = (fun i j => raw39735step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39735step1 raw39735step0; decide +kernel
      have hl : raw39735step1Labels = raw39735step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39735step0 raw39735step0Labels permutation151 permutation7
    _ = mixedMoment B node387 node387Labels := by rfl

def raw39736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw39736Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw39736step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39736step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39736 raw39736Labels = mixedMoment B node150 node150Labels := by
  calc
    mixedMoment B raw39736 raw39736Labels = mixedMoment B raw39736step0 raw39736step0Labels := by
      have hz : ∀ j, raw39736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39736step0 = (fun i j => raw39736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39736step0 raw39736; decide +kernel
      have hl : raw39736step0Labels = raw39736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39736 raw39736Labels permutation346 hz
    mixedMoment B raw39736step0 raw39736step0Labels = mixedMoment B raw39736step1 raw39736step1Labels := by
      have ha : raw39736step1 = (fun i j => raw39736step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39736step1 raw39736step0; decide +kernel
      have hl : raw39736step1Labels = raw39736step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39736step0 raw39736step0Labels permutation128 permutation6
    _ = mixedMoment B node150 node150Labels := by rfl

def raw39737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39737Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39737step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39737step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39737 raw39737Labels = mixedMoment B node145 node145Labels := by
  calc
    mixedMoment B raw39737 raw39737Labels = mixedMoment B raw39737step0 raw39737step0Labels := by
      have hz : ∀ j, raw39737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39737step0 = (fun i j => raw39737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39737step0 raw39737; decide +kernel
      have hl : raw39737step0Labels = raw39737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39737 raw39737Labels permutation346 hz
    mixedMoment B raw39737step0 raw39737step0Labels = mixedMoment B raw39737step1 raw39737step1Labels := by
      have ha : raw39737step1 = (fun i j => raw39737step0 (permutation148 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39737step1 raw39737step0; decide +kernel
      have hl : raw39737step1Labels = raw39737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39737step0 raw39737step0Labels permutation148 permutation7
    _ = mixedMoment B node145 node145Labels := by rfl

def raw39738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39738Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39738step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39738 raw39738Labels = mixedMoment B node330 node330Labels := by
  calc
    mixedMoment B raw39738 raw39738Labels = mixedMoment B raw39738step0 raw39738step0Labels := by
      have ha : raw39738step0 = (fun i j => raw39738 (permutation484 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39738step0 raw39738; decide +kernel
      have hl : raw39738step0Labels = raw39738Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39738 raw39738Labels permutation484 permutation6
    _ = mixedMoment B node330 node330Labels := by rfl

def raw39739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39739Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39739step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39739 raw39739Labels = mixedMoment B node394 node394Labels := by
  calc
    mixedMoment B raw39739 raw39739Labels = mixedMoment B raw39739step0 raw39739step0Labels := by
      have ha : raw39739step0 = (fun i j => raw39739 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39739step0 raw39739; decide +kernel
      have hl : raw39739step0Labels = raw39739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39739 raw39739Labels permutation499 permutation6
    _ = mixedMoment B node394 node394Labels := by rfl

def raw39740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39740Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39740step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39740step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39740step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39740 raw39740Labels = mixedMoment B node491 node491Labels := by
  calc
    mixedMoment B raw39740 raw39740Labels = mixedMoment B raw39740step0 raw39740step0Labels := by
      have hz : ∀ j, raw39740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39740step0 = (fun i j => raw39740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39740step0 raw39740; decide +kernel
      have hl : raw39740step0Labels = raw39740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39740 raw39740Labels permutation434 hz
    mixedMoment B raw39740step0 raw39740step0Labels = mixedMoment B raw39740step1 raw39740step1Labels := by
      have ha : raw39740step1 = (fun i j => raw39740step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39740step1 raw39740step0; decide +kernel
      have hl : raw39740step1Labels = raw39740step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39740step0 raw39740step0Labels permutation151 permutation3
    mixedMoment B raw39740step1 raw39740step1Labels = mixedMoment B raw39740step2 raw39740step2Labels := by
      have ha : raw39740step2 = -raw39740step1 := by apply Matrix.ext; change ∀ i j, raw39740step2 i j = -(raw39740step1 i j); unfold raw39740step2 raw39740step1; decide +kernel
      have hl : raw39740step2Labels = raw39740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node491 node491Labels := by rfl

def raw39741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39741Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39741step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39741step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39741 raw39741Labels = mixedMoment B node447 node447Labels := by
  calc
    mixedMoment B raw39741 raw39741Labels = mixedMoment B raw39741step0 raw39741step0Labels := by
      have hz : ∀ j, raw39741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39741step0 = (fun i j => raw39741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39741step0 raw39741; decide +kernel
      have hl : raw39741step0Labels = raw39741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39741 raw39741Labels permutation434 hz
    mixedMoment B raw39741step0 raw39741step0Labels = mixedMoment B raw39741step1 raw39741step1Labels := by
      have ha : raw39741step1 = (fun i j => raw39741step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39741step1 raw39741step0; decide +kernel
      have hl : raw39741step1Labels = raw39741step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39741step0 raw39741step0Labels permutation99 permutation6
    _ = mixedMoment B node447 node447Labels := by rfl

def raw39742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39742Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39742step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39742 raw39742Labels = mixedMoment B node470 node470Labels := by
  calc
    mixedMoment B raw39742 raw39742Labels = mixedMoment B raw39742step0 raw39742step0Labels := by
      have ha : raw39742step0 = (fun i j => raw39742 (permutation390 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39742step0 raw39742; decide +kernel
      have hl : raw39742step0Labels = raw39742Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39742 raw39742Labels permutation390 permutation6
    _ = mixedMoment B node470 node470Labels := by rfl

def raw39743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39743Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39743step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39743 raw39743Labels = mixedMoment B node484 node484Labels := by
  calc
    mixedMoment B raw39743 raw39743Labels = mixedMoment B raw39743step0 raw39743step0Labels := by
      have ha : raw39743step0 = (fun i j => raw39743 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39743step0 raw39743; decide +kernel
      have hl : raw39743step0Labels = raw39743Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39743 raw39743Labels permutation393 permutation6
    _ = mixedMoment B node484 node484Labels := by rfl

def raw39744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39744Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39744step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39744step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39744step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39744 raw39744Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw39744 raw39744Labels = mixedMoment B raw39744step0 raw39744step0Labels := by
      have hz : ∀ j, raw39744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39744step0 = (fun i j => raw39744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39744step0 raw39744; decide +kernel
      have hl : raw39744step0Labels = raw39744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39744 raw39744Labels permutation434 hz
    mixedMoment B raw39744step0 raw39744step0Labels = mixedMoment B raw39744step1 raw39744step1Labels := by
      have ha : raw39744step1 = (fun i j => raw39744step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39744step1 raw39744step0; decide +kernel
      have hl : raw39744step1Labels = raw39744step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39744step0 raw39744step0Labels permutation151 permutation2
    mixedMoment B raw39744step1 raw39744step1Labels = mixedMoment B raw39744step2 raw39744step2Labels := by
      have ha : raw39744step2 = -raw39744step1 := by apply Matrix.ext; change ∀ i j, raw39744step2 i j = -(raw39744step1 i j); unfold raw39744step2 raw39744step1; decide +kernel
      have hl : raw39744step2Labels = raw39744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node483 node483Labels := by rfl

def raw39745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39745Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39745step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw39745step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39745step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39745 raw39745Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39745 raw39745Labels = mixedMoment B raw39745step0 raw39745step0Labels := by
      have hz : ∀ j, raw39745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39745step0 = (fun i j => raw39745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39745step0 raw39745; decide +kernel
      have hl : raw39745step0Labels = raw39745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39745 raw39745Labels permutation434 hz
    mixedMoment B raw39745step0 raw39745step0Labels = mixedMoment B raw39745step1 raw39745step1Labels := by
      have hz : ∀ j, raw39745step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39745step1 = (fun i j => raw39745step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39745step1 raw39745step0; decide +kernel
      have hl : raw39745step1Labels = raw39745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39745step0 raw39745step0Labels permutation80 hz
    mixedMoment B raw39745step1 raw39745step1Labels = mixedMoment B raw39745step2 raw39745step2Labels := by
      have ha : raw39745step2 = (fun i j => raw39745step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39745step2 raw39745step1; decide +kernel
      have hl : raw39745step2Labels = raw39745step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39745step1 raw39745step1Labels permutation24 permutation6
    _ = mixedMoment B node410 node410Labels := by rfl

def raw39746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39746Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39746step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39746step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39746step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39746 raw39746Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw39746 raw39746Labels = mixedMoment B raw39746step0 raw39746step0Labels := by
      have hz : ∀ j, raw39746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39746step0 = (fun i j => raw39746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39746step0 raw39746; decide +kernel
      have hl : raw39746step0Labels = raw39746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39746 raw39746Labels permutation434 hz
    mixedMoment B raw39746step0 raw39746step0Labels = mixedMoment B raw39746step1 raw39746step1Labels := by
      have hz : ∀ j, raw39746step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39746step1 = (fun i j => raw39746step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39746step1 raw39746step0; decide +kernel
      have hl : raw39746step1Labels = raw39746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39746step0 raw39746step0Labels permutation80 hz
    mixedMoment B raw39746step1 raw39746step1Labels = mixedMoment B raw39746step2 raw39746step2Labels := by
      have ha : raw39746step2 = (fun i j => raw39746step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39746step2 raw39746step1; decide +kernel
      have hl : raw39746step2Labels = raw39746step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39746step1 raw39746step1Labels permutation30 permutation7
    _ = mixedMoment B node390 node390Labels := by rfl

def raw39747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39747Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39747step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw39747step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39747step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39747step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39747 raw39747Labels = mixedMoment B node153 node153Labels := by
  calc
    mixedMoment B raw39747 raw39747Labels = mixedMoment B raw39747step0 raw39747step0Labels := by
      have hz : ∀ j, raw39747 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39747step0 = (fun i j => raw39747 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39747step0 raw39747; decide +kernel
      have hl : raw39747step0Labels = raw39747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39747 raw39747Labels permutation434 hz
    mixedMoment B raw39747step0 raw39747step0Labels = mixedMoment B raw39747step1 raw39747step1Labels := by
      have hz : ∀ j, raw39747step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39747step1 = (fun i j => raw39747step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39747step1 raw39747step0; decide +kernel
      have hl : raw39747step1Labels = raw39747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39747step0 raw39747step0Labels permutation80 hz
    mixedMoment B raw39747step1 raw39747step1Labels = mixedMoment B raw39747step2 raw39747step2Labels := by
      have ha : raw39747step2 = (fun i j => raw39747step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39747step2 raw39747step1; decide +kernel
      have hl : raw39747step2Labels = raw39747step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39747step1 raw39747step1Labels permutation27 permutation6
    _ = mixedMoment B node153 node153Labels := by rfl

def raw39748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39748Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39748step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39748step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39748 raw39748Labels = mixedMoment B node333 node333Labels := by
  calc
    mixedMoment B raw39748 raw39748Labels = mixedMoment B raw39748step0 raw39748step0Labels := by
      have hz : ∀ j, raw39748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39748step0 = (fun i j => raw39748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39748step0 raw39748; decide +kernel
      have hl : raw39748step0Labels = raw39748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39748 raw39748Labels permutation346 hz
    mixedMoment B raw39748step0 raw39748step0Labels = mixedMoment B raw39748step1 raw39748step1Labels := by
      have ha : raw39748step1 = (fun i j => raw39748step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39748step1 raw39748step0; decide +kernel
      have hl : raw39748step1Labels = raw39748step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39748step0 raw39748step0Labels permutation93 permutation6
    _ = mixedMoment B node333 node333Labels := by rfl

def raw39749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39749Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39749step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39749step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39749 raw39749Labels = mixedMoment B node395 node395Labels := by
  calc
    mixedMoment B raw39749 raw39749Labels = mixedMoment B raw39749step0 raw39749step0Labels := by
      have hz : ∀ j, raw39749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39749step0 = (fun i j => raw39749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39749step0 raw39749; decide +kernel
      have hl : raw39749step0Labels = raw39749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39749 raw39749Labels permutation346 hz
    mixedMoment B raw39749step0 raw39749step0Labels = mixedMoment B raw39749step1 raw39749step1Labels := by
      have ha : raw39749step1 = (fun i j => raw39749step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39749step1 raw39749step0; decide +kernel
      have hl : raw39749step1Labels = raw39749step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39749step0 raw39749step0Labels permutation96 permutation6
    _ = mixedMoment B node395 node395Labels := by rfl

def raw39750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39750Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39750step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39750step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw39750step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39750 raw39750Labels = mixedMoment B node346 node346Labels := by
  calc
    mixedMoment B raw39750 raw39750Labels = mixedMoment B raw39750step0 raw39750step0Labels := by
      have hz : ∀ j, raw39750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39750step0 = (fun i j => raw39750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39750step0 raw39750; decide +kernel
      have hl : raw39750step0Labels = raw39750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39750 raw39750Labels permutation434 hz
    mixedMoment B raw39750step0 raw39750step0Labels = mixedMoment B raw39750step1 raw39750step1Labels := by
      have ha : raw39750step1 = (fun i j => raw39750step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39750step1 raw39750step0; decide +kernel
      have hl : raw39750step1Labels = raw39750step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39750step0 raw39750step0Labels permutation59 permutation6
    mixedMoment B raw39750step1 raw39750step1Labels = mixedMoment B raw39750step2 raw39750step2Labels := by
      have ha : raw39750step2 = -raw39750step1 := by apply Matrix.ext; change ∀ i j, raw39750step2 i j = -(raw39750step1 i j); unfold raw39750step2 raw39750step1; decide +kernel
      have hl : raw39750step2Labels = raw39750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node346 node346Labels := by rfl

def raw39751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39751Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39751step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw39751step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39751step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39751 raw39751Labels = mixedMoment B node147 node147Labels := by
  calc
    mixedMoment B raw39751 raw39751Labels = mixedMoment B raw39751step0 raw39751step0Labels := by
      have hz : ∀ j, raw39751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39751step0 = (fun i j => raw39751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39751step0 raw39751; decide +kernel
      have hl : raw39751step0Labels = raw39751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39751 raw39751Labels permutation434 hz
    mixedMoment B raw39751step0 raw39751step0Labels = mixedMoment B raw39751step1 raw39751step1Labels := by
      have hz : ∀ j, raw39751step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39751step1 = (fun i j => raw39751step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39751step1 raw39751step0; decide +kernel
      have hl : raw39751step1Labels = raw39751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39751step0 raw39751step0Labels permutation80 hz
    mixedMoment B raw39751step1 raw39751step1Labels = mixedMoment B raw39751step2 raw39751step2Labels := by
      have ha : raw39751step2 = (fun i j => raw39751step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39751step2 raw39751step1; decide +kernel
      have hl : raw39751step2Labels = raw39751step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39751step1 raw39751step1Labels permutation30 permutation7
    _ = mixedMoment B node147 node147Labels := by rfl

def raw39752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39752Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39752step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -3, 1]]
def raw39752step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39752step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, -3, 1]]
def raw39752step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39752step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39752step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39752 raw39752Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39752 raw39752Labels = mixedMoment B raw39752step0 raw39752step0Labels := by
      have hz : ∀ j, raw39752 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39752step0 = (fun i j => raw39752 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39752step0 raw39752; decide +kernel
      have hl : raw39752step0Labels = raw39752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39752 raw39752Labels permutation520 hz
    mixedMoment B raw39752step0 raw39752step0Labels = mixedMoment B raw39752step1 raw39752step1Labels := by
      have hz : ∀ j, raw39752step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39752step1 = (fun i j => raw39752step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39752step1 raw39752step0; decide +kernel
      have hl : raw39752step1Labels = raw39752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39752step0 raw39752step0Labels permutation104 hz
    mixedMoment B raw39752step1 raw39752step1Labels = mixedMoment B raw39752step2 raw39752step2Labels := by
      have hz : ∀ j, raw39752step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39752step2 = (fun i j => raw39752step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39752step2 raw39752step1; decide +kernel
      have hl : raw39752step2Labels = raw39752step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39752step1 raw39752step1Labels permutation20 hz
    mixedMoment B raw39752step2 raw39752step2Labels = mixedMoment B raw39752step3 raw39752step3Labels := by
      have ha : raw39752step3 = (fun i j => raw39752step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39752step3 raw39752step2; decide +kernel
      have hl : raw39752step3Labels = raw39752step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39752step2 raw39752step2Labels permutation6 permutation5
    _ = mixedMoment B node420 node420Labels := by rfl

def raw39753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39753Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39753step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0]]
def raw39753step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39753step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39753 raw39753Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39753 raw39753Labels = mixedMoment B raw39753step0 raw39753step0Labels := by
      have hz : ∀ j, raw39753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39753step0 = (fun i j => raw39753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39753step0 raw39753; decide +kernel
      have hl : raw39753step0Labels = raw39753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39753 raw39753Labels permutation434 hz
    mixedMoment B raw39753step0 raw39753step0Labels = mixedMoment B raw39753step1 raw39753step1Labels := by
      have hz : ∀ j, raw39753step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39753step1 = (fun i j => raw39753step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39753step1 raw39753step0; decide +kernel
      have hl : raw39753step1Labels = raw39753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39753step0 raw39753step0Labels permutation80 hz
    mixedMoment B raw39753step1 raw39753step1Labels = mixedMoment B raw39753step2 raw39753step2Labels := by
      have ha : raw39753step2 = (fun i j => raw39753step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39753step2 raw39753step1; decide +kernel
      have hl : raw39753step2Labels = raw39753step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39753step1 raw39753step1Labels permutation30 permutation5
    _ = mixedMoment B node496 node496Labels := by rfl

def raw39754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw39754Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw39754step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39754step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39754step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39754 raw39754Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw39754 raw39754Labels = mixedMoment B raw39754step0 raw39754step0Labels := by
      have hz : ∀ j, raw39754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39754step0 = (fun i j => raw39754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39754step0 raw39754; decide +kernel
      have hl : raw39754step0Labels = raw39754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39754 raw39754Labels permutation434 hz
    mixedMoment B raw39754step0 raw39754step0Labels = mixedMoment B raw39754step1 raw39754step1Labels := by
      have hz : ∀ j, raw39754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39754step1 = (fun i j => raw39754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39754step1 raw39754step0; decide +kernel
      have hl : raw39754step1Labels = raw39754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39754step0 raw39754step0Labels permutation80 hz
    mixedMoment B raw39754step1 raw39754step1Labels = mixedMoment B raw39754step2 raw39754step2Labels := by
      have ha : raw39754step2 = (fun i j => raw39754step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39754step2 raw39754step1; decide +kernel
      have hl : raw39754step2Labels = raw39754step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39754step1 raw39754step1Labels permutation30 permutation4
    _ = mixedMoment B node402 node402Labels := by rfl

def raw39755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39755Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39755step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39755step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39755step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39755step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39755step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39755step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39755 raw39755Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw39755 raw39755Labels = mixedMoment B raw39755step0 raw39755step0Labels := by
      have hz : ∀ j, raw39755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39755step0 = (fun i j => raw39755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39755step0 raw39755; decide +kernel
      have hl : raw39755step0Labels = raw39755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39755 raw39755Labels permutation434 hz
    mixedMoment B raw39755step0 raw39755step0Labels = mixedMoment B raw39755step1 raw39755step1Labels := by
      have hz : ∀ j, raw39755step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39755step1 = (fun i j => raw39755step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39755step1 raw39755step0; decide +kernel
      have hl : raw39755step1Labels = raw39755step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39755step0 raw39755step0Labels permutation80 hz
    mixedMoment B raw39755step1 raw39755step1Labels = mixedMoment B raw39755step2 raw39755step2Labels := by
      have ha : raw39755step2 = (fun i j => raw39755step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39755step2 raw39755step1; decide +kernel
      have hl : raw39755step2Labels = raw39755step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39755step1 raw39755step1Labels permutation14 permutation4
    mixedMoment B raw39755step2 raw39755step2Labels = mixedMoment B raw39755step3 raw39755step3Labels := by
      have ha : raw39755step3 = -raw39755step2 := by apply Matrix.ext; change ∀ i j, raw39755step3 i j = -(raw39755step2 i j); unfold raw39755step3 raw39755step2; decide +kernel
      have hl : raw39755step3Labels = raw39755step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node503 node503Labels := by rfl

def raw39756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39756Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39756step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39756step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39756 raw39756Labels = mixedMoment B node446 node446Labels := by
  calc
    mixedMoment B raw39756 raw39756Labels = mixedMoment B raw39756step0 raw39756step0Labels := by
      have hz : ∀ j, raw39756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39756step0 = (fun i j => raw39756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39756step0 raw39756; decide +kernel
      have hl : raw39756step0Labels = raw39756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39756 raw39756Labels permutation346 hz
    mixedMoment B raw39756step0 raw39756step0Labels = mixedMoment B raw39756step1 raw39756step1Labels := by
      have ha : raw39756step1 = (fun i j => raw39756step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39756step1 raw39756step0; decide +kernel
      have hl : raw39756step1Labels = raw39756step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39756step0 raw39756step0Labels permutation74 permutation6
    _ = mixedMoment B node446 node446Labels := by rfl

def raw39757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39757Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39757step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39757step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39757 raw39757Labels = mixedMoment B node493 node493Labels := by
  calc
    mixedMoment B raw39757 raw39757Labels = mixedMoment B raw39757step0 raw39757step0Labels := by
      have hz : ∀ j, raw39757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39757step0 = (fun i j => raw39757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39757step0 raw39757; decide +kernel
      have hl : raw39757step0Labels = raw39757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39757 raw39757Labels permutation346 hz
    mixedMoment B raw39757step0 raw39757step0Labels = mixedMoment B raw39757step1 raw39757step1Labels := by
      have ha : raw39757step1 = (fun i j => raw39757step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39757step1 raw39757step0; decide +kernel
      have hl : raw39757step1Labels = raw39757step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39757step0 raw39757step0Labels permutation68 permutation6
    _ = mixedMoment B node493 node493Labels := by rfl

def raw39758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39758Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39758step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39758step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39758 raw39758Labels = mixedMoment B node487 node487Labels := by
  calc
    mixedMoment B raw39758 raw39758Labels = mixedMoment B raw39758step0 raw39758step0Labels := by
      have hz : ∀ j, raw39758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39758step0 = (fun i j => raw39758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39758step0 raw39758; decide +kernel
      have hl : raw39758step0Labels = raw39758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39758 raw39758Labels permutation346 hz
    mixedMoment B raw39758step0 raw39758step0Labels = mixedMoment B raw39758step1 raw39758step1Labels := by
      have ha : raw39758step1 = (fun i j => raw39758step0 (permutation102 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39758step1 raw39758step0; decide +kernel
      have hl : raw39758step1Labels = raw39758step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39758step0 raw39758step0Labels permutation102 permutation4
    _ = mixedMoment B node487 node487Labels := by rfl

def raw39759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39759Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39759step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39759step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39759step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39759 raw39759Labels = mixedMoment B node244 node244Labels := by
  calc
    mixedMoment B raw39759 raw39759Labels = mixedMoment B raw39759step0 raw39759step0Labels := by
      have hz : ∀ j, raw39759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39759step0 = (fun i j => raw39759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39759step0 raw39759; decide +kernel
      have hl : raw39759step0Labels = raw39759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39759 raw39759Labels permutation346 hz
    mixedMoment B raw39759step0 raw39759step0Labels = mixedMoment B raw39759step1 raw39759step1Labels := by
      have ha : raw39759step1 = (fun i j => raw39759step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39759step1 raw39759step0; decide +kernel
      have hl : raw39759step1Labels = raw39759step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39759step0 raw39759step0Labels permutation83 permutation6
    mixedMoment B raw39759step1 raw39759step1Labels = mixedMoment B raw39759step2 raw39759step2Labels := by
      have ha : raw39759step2 = -raw39759step1 := by apply Matrix.ext; change ∀ i j, raw39759step2 i j = -(raw39759step1 i j); unfold raw39759step2 raw39759step1; decide +kernel
      have hl : raw39759step2Labels = raw39759step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node244 node244Labels := by rfl

def raw39760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39760Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39760step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39760step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39760 raw39760Labels = mixedMoment B node456 node456Labels := by
  calc
    mixedMoment B raw39760 raw39760Labels = mixedMoment B raw39760step0 raw39760step0Labels := by
      have ha : raw39760step0 = (fun i j => raw39760 (permutation468 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39760step0 raw39760; decide +kernel
      have hl : raw39760step0Labels = raw39760Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39760 raw39760Labels permutation468 permutation6
    mixedMoment B raw39760step0 raw39760step0Labels = mixedMoment B raw39760step1 raw39760step1Labels := by
      have ha : raw39760step1 = -raw39760step0 := by apply Matrix.ext; change ∀ i j, raw39760step1 i j = -(raw39760step0 i j); unfold raw39760step1 raw39760step0; decide +kernel
      have hl : raw39760step1Labels = raw39760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node456 node456Labels := by rfl

def raw39761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39761Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39761step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39761step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39761 raw39761Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw39761 raw39761Labels = mixedMoment B raw39761step0 raw39761step0Labels := by
      have hz : ∀ j, raw39761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39761step0 = (fun i j => raw39761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39761step0 raw39761; decide +kernel
      have hl : raw39761step0Labels = raw39761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39761 raw39761Labels permutation434 hz
    mixedMoment B raw39761step0 raw39761step0Labels = mixedMoment B raw39761step1 raw39761step1Labels := by
      have ha : raw39761step1 = (fun i j => raw39761step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39761step1 raw39761step0; decide +kernel
      have hl : raw39761step1Labels = raw39761step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39761step0 raw39761step0Labels permutation149 permutation5
    _ = mixedMoment B node494 node494Labels := by rfl

def raw39762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39762Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw39762step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39762step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39762step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39762 raw39762Labels = mixedMoment B node248 node248Labels := by
  calc
    mixedMoment B raw39762 raw39762Labels = mixedMoment B raw39762step0 raw39762step0Labels := by
      have hz : ∀ j, raw39762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39762step0 = (fun i j => raw39762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39762step0 raw39762; decide +kernel
      have hl : raw39762step0Labels = raw39762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39762 raw39762Labels permutation434 hz
    mixedMoment B raw39762step0 raw39762step0Labels = mixedMoment B raw39762step1 raw39762step1Labels := by
      have ha : raw39762step1 = (fun i j => raw39762step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39762step1 raw39762step0; decide +kernel
      have hl : raw39762step1Labels = raw39762step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39762step0 raw39762step0Labels permutation104 permutation6
    mixedMoment B raw39762step1 raw39762step1Labels = mixedMoment B raw39762step2 raw39762step2Labels := by
      have ha : raw39762step2 = -raw39762step1 := by apply Matrix.ext; change ∀ i j, raw39762step2 i j = -(raw39762step1 i j); unfold raw39762step2 raw39762step1; decide +kernel
      have hl : raw39762step2Labels = raw39762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node248 node248Labels := by rfl

def raw39763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39763Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39763step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39763step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39763 raw39763Labels = mixedMoment B node459 node459Labels := by
  calc
    mixedMoment B raw39763 raw39763Labels = mixedMoment B raw39763step0 raw39763step0Labels := by
      have ha : raw39763step0 = (fun i j => raw39763 (permutation553 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39763step0 raw39763; decide +kernel
      have hl : raw39763step0Labels = raw39763Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39763 raw39763Labels permutation553 permutation6
    mixedMoment B raw39763step0 raw39763step0Labels = mixedMoment B raw39763step1 raw39763step1Labels := by
      have ha : raw39763step1 = -raw39763step0 := by apply Matrix.ext; change ∀ i j, raw39763step1 i j = -(raw39763step0 i j); unfold raw39763step1 raw39763step0; decide +kernel
      have hl : raw39763step1Labels = raw39763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node459 node459Labels := by rfl

def raw39764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39764Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39764step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw39764step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw39764step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw39764step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw39764step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39764 raw39764Labels = mixedMoment B node5507 node5507Labels := by
  calc
    mixedMoment B raw39764 raw39764Labels = mixedMoment B raw39764step0 raw39764step0Labels := by
      have hz : ∀ j, raw39764 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39764step0 = (fun i j => raw39764 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39764step0 raw39764; decide +kernel
      have hl : raw39764step0Labels = raw39764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39764 raw39764Labels permutation520 hz
    mixedMoment B raw39764step0 raw39764step0Labels = mixedMoment B raw39764step1 raw39764step1Labels := by
      have hz : ∀ j, raw39764step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39764step1 = (fun i j => raw39764step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39764step1 raw39764step0; decide +kernel
      have hl : raw39764step1Labels = raw39764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39764step0 raw39764step0Labels permutation104 hz
    mixedMoment B raw39764step1 raw39764step1Labels = mixedMoment B raw39764step2 raw39764step2Labels := by
      have hz : ∀ j, raw39764step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39764step2 = (fun i j => raw39764step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39764step2 raw39764step1; decide +kernel
      have hl : raw39764step2Labels = raw39764step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39764step1 raw39764step1Labels permutation20 hz
    mixedMoment B raw39764step2 raw39764step2Labels = mixedMoment B raw39764step3 raw39764step3Labels := by
      have ha : raw39764step3 = (fun i j => raw39764step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39764step3 raw39764step2; decide +kernel
      have hl : raw39764step3Labels = raw39764step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39764step2 raw39764step2Labels permutation7 permutation3
    mixedMoment B raw39764step3 raw39764step3Labels = mixedMoment B raw39764step4 raw39764step4Labels := by
      have ha : raw39764step4 = -raw39764step3 := by apply Matrix.ext; change ∀ i j, raw39764step4 i j = -(raw39764step3 i j); unfold raw39764step4 raw39764step3; decide +kernel
      have hl : raw39764step4Labels = raw39764step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5507 node5507Labels := by rfl

def raw39765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39765Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39765step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw39765step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39765step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39765 raw39765Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39765 raw39765Labels = mixedMoment B raw39765step0 raw39765step0Labels := by
      have hz : ∀ j, raw39765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39765step0 = (fun i j => raw39765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39765step0 raw39765; decide +kernel
      have hl : raw39765step0Labels = raw39765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39765 raw39765Labels permutation434 hz
    mixedMoment B raw39765step0 raw39765step0Labels = mixedMoment B raw39765step1 raw39765step1Labels := by
      have hz : ∀ j, raw39765step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39765step1 = (fun i j => raw39765step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39765step1 raw39765step0; decide +kernel
      have hl : raw39765step1Labels = raw39765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39765step0 raw39765step0Labels permutation80 hz
    mixedMoment B raw39765step1 raw39765step1Labels = mixedMoment B raw39765step2 raw39765step2Labels := by
      have ha : raw39765step2 = (fun i j => raw39765step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39765step2 raw39765step1; decide +kernel
      have hl : raw39765step2Labels = raw39765step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39765step1 raw39765step1Labels permutation28 permutation7
    _ = mixedMoment B node496 node496Labels := by rfl

def raw39766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw39766Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw39766step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw39766step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw39766step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39766step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39766step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39766 raw39766Labels = mixedMoment B node249 node249Labels := by
  calc
    mixedMoment B raw39766 raw39766Labels = mixedMoment B raw39766step0 raw39766step0Labels := by
      have hz : ∀ j, raw39766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39766step0 = (fun i j => raw39766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39766step0 raw39766; decide +kernel
      have hl : raw39766step0Labels = raw39766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39766 raw39766Labels permutation434 hz
    mixedMoment B raw39766step0 raw39766step0Labels = mixedMoment B raw39766step1 raw39766step1Labels := by
      have hz : ∀ j, raw39766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39766step1 = (fun i j => raw39766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39766step1 raw39766step0; decide +kernel
      have hl : raw39766step1Labels = raw39766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39766step0 raw39766step0Labels permutation80 hz
    mixedMoment B raw39766step1 raw39766step1Labels = mixedMoment B raw39766step2 raw39766step2Labels := by
      have ha : raw39766step2 = (fun i j => raw39766step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39766step2 raw39766step1; decide +kernel
      have hl : raw39766step2Labels = raw39766step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39766step1 raw39766step1Labels permutation20 permutation6
    mixedMoment B raw39766step2 raw39766step2Labels = mixedMoment B raw39766step3 raw39766step3Labels := by
      have ha : raw39766step3 = -raw39766step2 := by apply Matrix.ext; change ∀ i j, raw39766step3 i j = -(raw39766step2 i j); unfold raw39766step3 raw39766step2; decide +kernel
      have hl : raw39766step3Labels = raw39766step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node249 node249Labels := by rfl

def raw39767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39767Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39767step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39767step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39767 raw39767Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw39767 raw39767Labels = mixedMoment B raw39767step0 raw39767step0Labels := by
      have hz : ∀ j, raw39767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39767step0 = (fun i j => raw39767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39767step0 raw39767; decide +kernel
      have hl : raw39767step0Labels = raw39767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39767 raw39767Labels permutation346 hz
    mixedMoment B raw39767step0 raw39767step0Labels = mixedMoment B raw39767step1 raw39767step1Labels := by
      have ha : raw39767step1 = (fun i j => raw39767step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39767step1 raw39767step0; decide +kernel
      have hl : raw39767step1Labels = raw39767step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39767step0 raw39767step0Labels permutation137 permutation7
    _ = mixedMoment B node494 node494Labels := by rfl

def raw39768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39768Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39768step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39768step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39768 raw39768Labels = mixedMoment B node337 node337Labels := by
  calc
    mixedMoment B raw39768 raw39768Labels = mixedMoment B raw39768step0 raw39768step0Labels := by
      have hz : ∀ j, raw39768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39768step0 = (fun i j => raw39768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39768step0 raw39768; decide +kernel
      have hl : raw39768step0Labels = raw39768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39768 raw39768Labels permutation346 hz
    mixedMoment B raw39768step0 raw39768step0Labels = mixedMoment B raw39768step1 raw39768step1Labels := by
      have ha : raw39768step1 = (fun i j => raw39768step0 (permutation136 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39768step1 raw39768step0; decide +kernel
      have hl : raw39768step1Labels = raw39768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39768step0 raw39768step0Labels permutation136 permutation7
    _ = mixedMoment B node337 node337Labels := by rfl

def raw39769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39769Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39769step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39769step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39769step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39769step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39769step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39769step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39769 raw39769Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39769 raw39769Labels = mixedMoment B raw39769step0 raw39769step0Labels := by
      have hz : ∀ j, raw39769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39769step0 = (fun i j => raw39769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39769step0 raw39769; decide +kernel
      have hl : raw39769step0Labels = raw39769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39769 raw39769Labels permutation434 hz
    mixedMoment B raw39769step0 raw39769step0Labels = mixedMoment B raw39769step1 raw39769step1Labels := by
      have hz : ∀ j, raw39769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39769step1 = (fun i j => raw39769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39769step1 raw39769step0; decide +kernel
      have hl : raw39769step1Labels = raw39769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39769step0 raw39769step0Labels permutation80 hz
    mixedMoment B raw39769step1 raw39769step1Labels = mixedMoment B raw39769step2 raw39769step2Labels := by
      have hz : ∀ j, raw39769step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39769step2 = (fun i j => raw39769step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39769step2 raw39769step1; decide +kernel
      have hl : raw39769step2Labels = raw39769step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39769step1 raw39769step1Labels permutation14 hz
    mixedMoment B raw39769step2 raw39769step2Labels = mixedMoment B raw39769step3 raw39769step3Labels := by
      have ha : raw39769step3 = (fun i j => raw39769step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39769step3 raw39769step2; decide +kernel
      have hl : raw39769step3Labels = raw39769step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39769step2 raw39769step2Labels permutation6 permutation7
    _ = mixedMoment B node420 node420Labels := by rfl

def raw39770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39770Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39770step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39770step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39770step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 2, -3], ![1, -3, 2]]
def raw39770step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39770step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39770step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39770 raw39770Labels = mixedMoment B node415 node415Labels := by
  calc
    mixedMoment B raw39770 raw39770Labels = mixedMoment B raw39770step0 raw39770step0Labels := by
      have hz : ∀ j, raw39770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39770step0 = (fun i j => raw39770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39770step0 raw39770; decide +kernel
      have hl : raw39770step0Labels = raw39770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39770 raw39770Labels permutation434 hz
    mixedMoment B raw39770step0 raw39770step0Labels = mixedMoment B raw39770step1 raw39770step1Labels := by
      have hz : ∀ j, raw39770step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39770step1 = (fun i j => raw39770step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39770step1 raw39770step0; decide +kernel
      have hl : raw39770step1Labels = raw39770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39770step0 raw39770step0Labels permutation80 hz
    mixedMoment B raw39770step1 raw39770step1Labels = mixedMoment B raw39770step2 raw39770step2Labels := by
      have hz : ∀ j, raw39770step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39770step2 = (fun i j => raw39770step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39770step2 raw39770step1; decide +kernel
      have hl : raw39770step2Labels = raw39770step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39770step1 raw39770step1Labels permutation14 hz
    mixedMoment B raw39770step2 raw39770step2Labels = mixedMoment B raw39770step3 raw39770step3Labels := by
      have ha : raw39770step3 = (fun i j => raw39770step2 (permutation6 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39770step3 raw39770step2; decide +kernel
      have hl : raw39770step3Labels = raw39770step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39770step2 raw39770step2Labels permutation6 permutation4
    _ = mixedMoment B node415 node415Labels := by rfl

def raw39771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39771Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39771step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39771step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39771step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39771 raw39771Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw39771 raw39771Labels = mixedMoment B raw39771step0 raw39771step0Labels := by
      have hz : ∀ j, raw39771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39771step0 = (fun i j => raw39771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39771step0 raw39771; decide +kernel
      have hl : raw39771step0Labels = raw39771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39771 raw39771Labels permutation346 hz
    mixedMoment B raw39771step0 raw39771step0Labels = mixedMoment B raw39771step1 raw39771step1Labels := by
      have hz : ∀ j, raw39771step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39771step1 = (fun i j => raw39771step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39771step1 raw39771step0; decide +kernel
      have hl : raw39771step1Labels = raw39771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39771step0 raw39771step0Labels permutation56 hz
    mixedMoment B raw39771step1 raw39771step1Labels = mixedMoment B raw39771step2 raw39771step2Labels := by
      have ha : raw39771step2 = (fun i j => raw39771step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39771step2 raw39771step1; decide +kernel
      have hl : raw39771step2Labels = raw39771step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39771step1 raw39771step1Labels permutation29 permutation7
    _ = mixedMoment B node416 node416Labels := by rfl

def raw39772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39772Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39772step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39772step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39772step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39772step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39772 raw39772Labels = mixedMoment B node152 node152Labels := by
  calc
    mixedMoment B raw39772 raw39772Labels = mixedMoment B raw39772step0 raw39772step0Labels := by
      have hz : ∀ j, raw39772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39772step0 = (fun i j => raw39772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39772step0 raw39772; decide +kernel
      have hl : raw39772step0Labels = raw39772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39772 raw39772Labels permutation346 hz
    mixedMoment B raw39772step0 raw39772step0Labels = mixedMoment B raw39772step1 raw39772step1Labels := by
      have hz : ∀ j, raw39772step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39772step1 = (fun i j => raw39772step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39772step1 raw39772step0; decide +kernel
      have hl : raw39772step1Labels = raw39772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39772step0 raw39772step0Labels permutation56 hz
    mixedMoment B raw39772step1 raw39772step1Labels = mixedMoment B raw39772step2 raw39772step2Labels := by
      have ha : raw39772step2 = (fun i j => raw39772step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39772step2 raw39772step1; decide +kernel
      have hl : raw39772step2Labels = raw39772step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39772step1 raw39772step1Labels permutation26 permutation6
    _ = mixedMoment B node152 node152Labels := by rfl

def raw39773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39773Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39773step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39773step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39773step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39773 raw39773Labels = mixedMoment B node414 node414Labels := by
  calc
    mixedMoment B raw39773 raw39773Labels = mixedMoment B raw39773step0 raw39773step0Labels := by
      have hz : ∀ j, raw39773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39773step0 = (fun i j => raw39773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39773step0 raw39773; decide +kernel
      have hl : raw39773step0Labels = raw39773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39773 raw39773Labels permutation346 hz
    mixedMoment B raw39773step0 raw39773step0Labels = mixedMoment B raw39773step1 raw39773step1Labels := by
      have hz : ∀ j, raw39773step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39773step1 = (fun i j => raw39773step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39773step1 raw39773step0; decide +kernel
      have hl : raw39773step1Labels = raw39773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39773step0 raw39773step0Labels permutation56 hz
    mixedMoment B raw39773step1 raw39773step1Labels = mixedMoment B raw39773step2 raw39773step2Labels := by
      have ha : raw39773step2 = (fun i j => raw39773step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39773step2 raw39773step1; decide +kernel
      have hl : raw39773step2Labels = raw39773step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39773step1 raw39773step1Labels permutation20 permutation6
    _ = mixedMoment B node414 node414Labels := by rfl

def raw39774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39774Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39774step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39774step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39774step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39774 raw39774Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw39774 raw39774Labels = mixedMoment B raw39774step0 raw39774step0Labels := by
      have hz : ∀ j, raw39774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39774step0 = (fun i j => raw39774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39774step0 raw39774; decide +kernel
      have hl : raw39774step0Labels = raw39774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39774 raw39774Labels permutation346 hz
    mixedMoment B raw39774step0 raw39774step0Labels = mixedMoment B raw39774step1 raw39774step1Labels := by
      have hz : ∀ j, raw39774step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39774step1 = (fun i j => raw39774step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39774step1 raw39774step0; decide +kernel
      have hl : raw39774step1Labels = raw39774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39774step0 raw39774step0Labels permutation56 hz
    mixedMoment B raw39774step1 raw39774step1Labels = mixedMoment B raw39774step2 raw39774step2Labels := by
      have ha : raw39774step2 = (fun i j => raw39774step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39774step2 raw39774step1; decide +kernel
      have hl : raw39774step2Labels = raw39774step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39774step1 raw39774step1Labels permutation24 permutation6
    _ = mixedMoment B node402 node402Labels := by rfl

def raw39775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39775Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39775step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39775step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw39775step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39775step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39775 raw39775Labels = mixedMoment B node247 node247Labels := by
  calc
    mixedMoment B raw39775 raw39775Labels = mixedMoment B raw39775step0 raw39775step0Labels := by
      have hz : ∀ j, raw39775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39775step0 = (fun i j => raw39775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39775step0 raw39775; decide +kernel
      have hl : raw39775step0Labels = raw39775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39775 raw39775Labels permutation346 hz
    mixedMoment B raw39775step0 raw39775step0Labels = mixedMoment B raw39775step1 raw39775step1Labels := by
      have hz : ∀ j, raw39775step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39775step1 = (fun i j => raw39775step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39775step1 raw39775step0; decide +kernel
      have hl : raw39775step1Labels = raw39775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39775step0 raw39775step0Labels permutation56 hz
    mixedMoment B raw39775step1 raw39775step1Labels = mixedMoment B raw39775step2 raw39775step2Labels := by
      have ha : raw39775step2 = (fun i j => raw39775step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39775step2 raw39775step1; decide +kernel
      have hl : raw39775step2Labels = raw39775step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39775step1 raw39775step1Labels permutation15 permutation6
    mixedMoment B raw39775step2 raw39775step2Labels = mixedMoment B raw39775step3 raw39775step3Labels := by
      have ha : raw39775step3 = -raw39775step2 := by apply Matrix.ext; change ∀ i j, raw39775step3 i j = -(raw39775step2 i j); unfold raw39775step3 raw39775step2; decide +kernel
      have hl : raw39775step3Labels = raw39775step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node247 node247Labels := by rfl

def raw39776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39776Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39776step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![3, -3, 0]]
def raw39776step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39776step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw39776step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39776step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39776step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39776 raw39776Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39776 raw39776Labels = mixedMoment B raw39776step0 raw39776step0Labels := by
      have hz : ∀ j, raw39776 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39776step0 = (fun i j => raw39776 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39776step0 raw39776; decide +kernel
      have hl : raw39776step0Labels = raw39776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39776 raw39776Labels permutation520 hz
    mixedMoment B raw39776step0 raw39776step0Labels = mixedMoment B raw39776step1 raw39776step1Labels := by
      have hz : ∀ j, raw39776step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39776step1 = (fun i j => raw39776step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39776step1 raw39776step0; decide +kernel
      have hl : raw39776step1Labels = raw39776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39776step0 raw39776step0Labels permutation104 hz
    mixedMoment B raw39776step1 raw39776step1Labels = mixedMoment B raw39776step2 raw39776step2Labels := by
      have hz : ∀ j, raw39776step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39776step2 = (fun i j => raw39776step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39776step2 raw39776step1; decide +kernel
      have hl : raw39776step2Labels = raw39776step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39776step1 raw39776step1Labels permutation20 hz
    mixedMoment B raw39776step2 raw39776step2Labels = mixedMoment B raw39776step3 raw39776step3Labels := by
      have ha : raw39776step3 = (fun i j => raw39776step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39776step3 raw39776step2; decide +kernel
      have hl : raw39776step3Labels = raw39776step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39776step2 raw39776step2Labels permutation6 permutation5
    _ = mixedMoment B node270 node270Labels := by rfl

def raw39777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39777Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39777step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39777step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39777step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39777step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39777step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39777 raw39777Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39777 raw39777Labels = mixedMoment B raw39777step0 raw39777step0Labels := by
      have hz : ∀ j, raw39777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39777step0 = (fun i j => raw39777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39777step0 raw39777; decide +kernel
      have hl : raw39777step0Labels = raw39777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39777 raw39777Labels permutation434 hz
    mixedMoment B raw39777step0 raw39777step0Labels = mixedMoment B raw39777step1 raw39777step1Labels := by
      have hz : ∀ j, raw39777step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39777step1 = (fun i j => raw39777step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39777step1 raw39777step0; decide +kernel
      have hl : raw39777step1Labels = raw39777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39777step0 raw39777step0Labels permutation80 hz
    mixedMoment B raw39777step1 raw39777step1Labels = mixedMoment B raw39777step2 raw39777step2Labels := by
      have ha : raw39777step2 = (fun i j => raw39777step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39777step2 raw39777step1; decide +kernel
      have hl : raw39777step2Labels = raw39777step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39777step1 raw39777step1Labels permutation14 permutation4
    mixedMoment B raw39777step2 raw39777step2Labels = mixedMoment B raw39777step3 raw39777step3Labels := by
      have ha : raw39777step3 = -raw39777step2 := by apply Matrix.ext; change ∀ i j, raw39777step3 i j = -(raw39777step2 i j); unfold raw39777step3 raw39777step2; decide +kernel
      have hl : raw39777step3Labels = raw39777step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node412 node412Labels := by rfl

def raw39778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39778Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39778step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39778step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39778step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39778step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39778step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39778 raw39778Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39778 raw39778Labels = mixedMoment B raw39778step0 raw39778step0Labels := by
      have hz : ∀ j, raw39778 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39778step0 = (fun i j => raw39778 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39778step0 raw39778; decide +kernel
      have hl : raw39778step0Labels = raw39778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39778 raw39778Labels permutation434 hz
    mixedMoment B raw39778step0 raw39778step0Labels = mixedMoment B raw39778step1 raw39778step1Labels := by
      have hz : ∀ j, raw39778step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39778step1 = (fun i j => raw39778step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39778step1 raw39778step0; decide +kernel
      have hl : raw39778step1Labels = raw39778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39778step0 raw39778step0Labels permutation80 hz
    mixedMoment B raw39778step1 raw39778step1Labels = mixedMoment B raw39778step2 raw39778step2Labels := by
      have ha : raw39778step2 = (fun i j => raw39778step1 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39778step2 raw39778step1; decide +kernel
      have hl : raw39778step2Labels = raw39778step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39778step1 raw39778step1Labels permutation15 permutation4
    mixedMoment B raw39778step2 raw39778step2Labels = mixedMoment B raw39778step3 raw39778step3Labels := by
      have ha : raw39778step3 = -raw39778step2 := by apply Matrix.ext; change ∀ i j, raw39778step3 i j = -(raw39778step2 i j); unfold raw39778step3 raw39778step2; decide +kernel
      have hl : raw39778step3Labels = raw39778step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node410 node410Labels := by rfl

def raw39779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39779Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39779step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]
def raw39779step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw39779step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39779 raw39779Labels = mixedMoment B node366 node366Labels := by
  calc
    mixedMoment B raw39779 raw39779Labels = mixedMoment B raw39779step0 raw39779step0Labels := by
      have hz : ∀ j, raw39779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39779step0 = (fun i j => raw39779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39779step0 raw39779; decide +kernel
      have hl : raw39779step0Labels = raw39779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39779 raw39779Labels permutation434 hz
    mixedMoment B raw39779step0 raw39779step0Labels = mixedMoment B raw39779step1 raw39779step1Labels := by
      have hz : ∀ j, raw39779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39779step1 = (fun i j => raw39779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39779step1 raw39779step0; decide +kernel
      have hl : raw39779step1Labels = raw39779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39779step0 raw39779step0Labels permutation80 hz
    mixedMoment B raw39779step1 raw39779step1Labels = mixedMoment B raw39779step2 raw39779step2Labels := by
      have ha : raw39779step2 = (fun i j => raw39779step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39779step2 raw39779step1; decide +kernel
      have hl : raw39779step2Labels = raw39779step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39779step1 raw39779step1Labels permutation21 permutation4
    _ = mixedMoment B node366 node366Labels := by rfl

def raw39780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39780Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39780step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39780step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39780step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39780 raw39780Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39780 raw39780Labels = mixedMoment B raw39780step0 raw39780step0Labels := by
      have hz : ∀ j, raw39780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39780step0 = (fun i j => raw39780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39780step0 raw39780; decide +kernel
      have hl : raw39780step0Labels = raw39780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39780 raw39780Labels permutation346 hz
    mixedMoment B raw39780step0 raw39780step0Labels = mixedMoment B raw39780step1 raw39780step1Labels := by
      have ha : raw39780step1 = (fun i j => raw39780step0 (permutation68 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39780step1 raw39780step0; decide +kernel
      have hl : raw39780step1Labels = raw39780step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39780step0 raw39780step0Labels permutation68 permutation4
    mixedMoment B raw39780step1 raw39780step1Labels = mixedMoment B raw39780step2 raw39780step2Labels := by
      have ha : raw39780step2 = -raw39780step1 := by apply Matrix.ext; change ∀ i j, raw39780step2 i j = -(raw39780step1 i j); unfold raw39780step2 raw39780step1; decide +kernel
      have hl : raw39780step2Labels = raw39780step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node384 node384Labels := by rfl

def raw39781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39781Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39781step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39781step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39781step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39781 raw39781Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39781 raw39781Labels = mixedMoment B raw39781step0 raw39781step0Labels := by
      have hz : ∀ j, raw39781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39781step0 = (fun i j => raw39781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39781step0 raw39781; decide +kernel
      have hl : raw39781step0Labels = raw39781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39781 raw39781Labels permutation346 hz
    mixedMoment B raw39781step0 raw39781step0Labels = mixedMoment B raw39781step1 raw39781step1Labels := by
      have ha : raw39781step1 = (fun i j => raw39781step0 (permutation61 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39781step1 raw39781step0; decide +kernel
      have hl : raw39781step1Labels = raw39781step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39781step0 raw39781step0Labels permutation61 permutation4
    mixedMoment B raw39781step1 raw39781step1Labels = mixedMoment B raw39781step2 raw39781step2Labels := by
      have ha : raw39781step2 = -raw39781step1 := by apply Matrix.ext; change ∀ i j, raw39781step2 i j = -(raw39781step1 i j); unfold raw39781step2 raw39781step1; decide +kernel
      have hl : raw39781step2Labels = raw39781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node409 node409Labels := by rfl

def raw39782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39782Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39782step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw39782step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw39782step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39782 raw39782Labels = mixedMoment B node365 node365Labels := by
  calc
    mixedMoment B raw39782 raw39782Labels = mixedMoment B raw39782step0 raw39782step0Labels := by
      have hz : ∀ j, raw39782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39782step0 = (fun i j => raw39782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39782step0 raw39782; decide +kernel
      have hl : raw39782step0Labels = raw39782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39782 raw39782Labels permutation346 hz
    mixedMoment B raw39782step0 raw39782step0Labels = mixedMoment B raw39782step1 raw39782step1Labels := by
      have ha : raw39782step1 = (fun i j => raw39782step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39782step1 raw39782step0; decide +kernel
      have hl : raw39782step1Labels = raw39782step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39782step0 raw39782step0Labels permutation74 permutation4
    mixedMoment B raw39782step1 raw39782step1Labels = mixedMoment B raw39782step2 raw39782step2Labels := by
      have ha : raw39782step2 = -raw39782step1 := by apply Matrix.ext; change ∀ i j, raw39782step2 i j = -(raw39782step1 i j); unfold raw39782step2 raw39782step1; decide +kernel
      have hl : raw39782step2Labels = raw39782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node365 node365Labels := by rfl

def raw39783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39783Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39783step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw39783step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39783step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39783 raw39783Labels = mixedMoment B node364 node364Labels := by
  calc
    mixedMoment B raw39783 raw39783Labels = mixedMoment B raw39783step0 raw39783step0Labels := by
      have hz : ∀ j, raw39783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39783step0 = (fun i j => raw39783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39783step0 raw39783; decide +kernel
      have hl : raw39783step0Labels = raw39783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39783 raw39783Labels permutation346 hz
    mixedMoment B raw39783step0 raw39783step0Labels = mixedMoment B raw39783step1 raw39783step1Labels := by
      have ha : raw39783step1 = (fun i j => raw39783step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39783step1 raw39783step0; decide +kernel
      have hl : raw39783step1Labels = raw39783step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39783step0 raw39783step0Labels permutation75 permutation4
    mixedMoment B raw39783step1 raw39783step1Labels = mixedMoment B raw39783step2 raw39783step2Labels := by
      have ha : raw39783step2 = -raw39783step1 := by apply Matrix.ext; change ∀ i j, raw39783step2 i j = -(raw39783step1 i j); unfold raw39783step2 raw39783step1; decide +kernel
      have hl : raw39783step2Labels = raw39783step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node364 node364Labels := by rfl

def raw39784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39784Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39784step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39784step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39784 raw39784Labels = mixedMoment B node363 node363Labels := by
  calc
    mixedMoment B raw39784 raw39784Labels = mixedMoment B raw39784step0 raw39784step0Labels := by
      have ha : raw39784step0 = (fun i j => raw39784 (permutation337 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39784step0 raw39784; decide +kernel
      have hl : raw39784step0Labels = raw39784Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39784 raw39784Labels permutation337 permutation4
    mixedMoment B raw39784step0 raw39784step0Labels = mixedMoment B raw39784step1 raw39784step1Labels := by
      have ha : raw39784step1 = -raw39784step0 := by apply Matrix.ext; change ∀ i j, raw39784step1 i j = -(raw39784step0 i j); unfold raw39784step1 raw39784step0; decide +kernel
      have hl : raw39784step1Labels = raw39784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node363 node363Labels := by rfl

def raw39785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39785Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39785step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw39785step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39785step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39785step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39785step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39785 raw39785Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39785 raw39785Labels = mixedMoment B raw39785step0 raw39785step0Labels := by
      have hz : ∀ j, raw39785 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39785step0 = (fun i j => raw39785 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39785step0 raw39785; decide +kernel
      have hl : raw39785step0Labels = raw39785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39785 raw39785Labels permutation520 hz
    mixedMoment B raw39785step0 raw39785step0Labels = mixedMoment B raw39785step1 raw39785step1Labels := by
      have hz : ∀ j, raw39785step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39785step1 = (fun i j => raw39785step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39785step1 raw39785step0; decide +kernel
      have hl : raw39785step1Labels = raw39785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39785step0 raw39785step0Labels permutation104 hz
    mixedMoment B raw39785step1 raw39785step1Labels = mixedMoment B raw39785step2 raw39785step2Labels := by
      have ha : raw39785step2 = (fun i j => raw39785step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39785step2 raw39785step1; decide +kernel
      have hl : raw39785step2Labels = raw39785step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39785step1 raw39785step1Labels permutation31 permutation3
    mixedMoment B raw39785step2 raw39785step2Labels = mixedMoment B raw39785step3 raw39785step3Labels := by
      have ha : raw39785step3 = -raw39785step2 := by apply Matrix.ext; change ∀ i j, raw39785step3 i j = -(raw39785step2 i j); unfold raw39785step3 raw39785step2; decide +kernel
      have hl : raw39785step3Labels = raw39785step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node268 node268Labels := by rfl

def raw39786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39786Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw39786step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39786step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39786 raw39786Labels = mixedMoment B node383 node383Labels := by
  calc
    mixedMoment B raw39786 raw39786Labels = mixedMoment B raw39786step0 raw39786step0Labels := by
      have hz : ∀ j, raw39786 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39786step0 = (fun i j => raw39786 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39786step0 raw39786; decide +kernel
      have hl : raw39786step0Labels = raw39786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39786 raw39786Labels permutation434 hz
    mixedMoment B raw39786step0 raw39786step0Labels = mixedMoment B raw39786step1 raw39786step1Labels := by
      have ha : raw39786step1 = (fun i j => raw39786step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39786step1 raw39786step0; decide +kernel
      have hl : raw39786step1Labels = raw39786step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39786step0 raw39786step0Labels permutation147 permutation5
    _ = mixedMoment B node383 node383Labels := by rfl

def raw39787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39787Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39787step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39787step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39787step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39787 raw39787Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39787 raw39787Labels = mixedMoment B raw39787step0 raw39787step0Labels := by
      have hz : ∀ j, raw39787 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39787step0 = (fun i j => raw39787 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39787step0 raw39787; decide +kernel
      have hl : raw39787step0Labels = raw39787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39787 raw39787Labels permutation434 hz
    mixedMoment B raw39787step0 raw39787step0Labels = mixedMoment B raw39787step1 raw39787step1Labels := by
      have ha : raw39787step1 = (fun i j => raw39787step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39787step1 raw39787step0; decide +kernel
      have hl : raw39787step1Labels = raw39787step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39787step0 raw39787step0Labels permutation151 permutation3
    mixedMoment B raw39787step1 raw39787step1Labels = mixedMoment B raw39787step2 raw39787step2Labels := by
      have ha : raw39787step2 = -raw39787step1 := by apply Matrix.ext; change ∀ i j, raw39787step2 i j = -(raw39787step1 i j); unfold raw39787step2 raw39787step1; decide +kernel
      have hl : raw39787step2Labels = raw39787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node467 node467Labels := by rfl

def raw39788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39788Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39788step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39788 raw39788Labels = mixedMoment B node498 node498Labels := by
  calc
    mixedMoment B raw39788 raw39788Labels = mixedMoment B raw39788step0 raw39788step0Labels := by
      have hz : ∀ j, raw39788 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39788step0 = (fun i j => raw39788 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39788step0 raw39788; decide +kernel
      have hl : raw39788step0Labels = raw39788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39788 raw39788Labels permutation434 hz
    _ = mixedMoment B node498 node498Labels := by rfl

def raw39789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39789Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39789step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw39789step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39789 raw39789Labels = mixedMoment B node365 node365Labels := by
  calc
    mixedMoment B raw39789 raw39789Labels = mixedMoment B raw39789step0 raw39789step0Labels := by
      have hz : ∀ j, raw39789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39789step0 = (fun i j => raw39789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39789step0 raw39789; decide +kernel
      have hl : raw39789step0Labels = raw39789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39789 raw39789Labels permutation434 hz
    mixedMoment B raw39789step0 raw39789step0Labels = mixedMoment B raw39789step1 raw39789step1Labels := by
      have ha : raw39789step1 = (fun i j => raw39789step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39789step1 raw39789step0; decide +kernel
      have hl : raw39789step1Labels = raw39789step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39789step0 raw39789step0Labels permutation109 permutation4
    _ = mixedMoment B node365 node365Labels := by rfl

def raw39790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39790Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39790step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39790step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39790 raw39790Labels = mixedMoment B node480 node480Labels := by
  calc
    mixedMoment B raw39790 raw39790Labels = mixedMoment B raw39790step0 raw39790step0Labels := by
      have ha : raw39790step0 = (fun i j => raw39790 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39790step0 raw39790; decide +kernel
      have hl : raw39790step0Labels = raw39790Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39790 raw39790Labels permutation688 permutation3
    mixedMoment B raw39790step0 raw39790step0Labels = mixedMoment B raw39790step1 raw39790step1Labels := by
      have ha : raw39790step1 = -raw39790step0 := by apply Matrix.ext; change ∀ i j, raw39790step1 i j = -(raw39790step0 i j); unfold raw39790step1 raw39790step0; decide +kernel
      have hl : raw39790step1Labels = raw39790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node480 node480Labels := by rfl

def raw39791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39791Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39791step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39791 raw39791Labels = mixedMoment B node475 node475Labels := by
  calc
    mixedMoment B raw39791 raw39791Labels = mixedMoment B raw39791step0 raw39791step0Labels := by
      have ha : raw39791step0 = (fun i j => raw39791 (permutation634 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39791step0 raw39791; decide +kernel
      have hl : raw39791step0Labels = raw39791Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39791 raw39791Labels permutation634 permutation7
    _ = mixedMoment B node475 node475Labels := by rfl

def raw39792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39792Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39792step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39792step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39792 raw39792Labels = mixedMoment B node443 node443Labels := by
  calc
    mixedMoment B raw39792 raw39792Labels = mixedMoment B raw39792step0 raw39792step0Labels := by
      have ha : raw39792step0 = (fun i j => raw39792 (permutation445 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39792step0 raw39792; decide +kernel
      have hl : raw39792step0Labels = raw39792Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39792 raw39792Labels permutation445 permutation6
    mixedMoment B raw39792step0 raw39792step0Labels = mixedMoment B raw39792step1 raw39792step1Labels := by
      have ha : raw39792step1 = -raw39792step0 := by apply Matrix.ext; change ∀ i j, raw39792step1 i j = -(raw39792step0 i j); unfold raw39792step1 raw39792step0; decide +kernel
      have hl : raw39792step1Labels = raw39792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node443 node443Labels := by rfl

def raw39793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39793Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39793step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39793 raw39793Labels = mixedMoment B node497 node497Labels := by
  calc
    mixedMoment B raw39793 raw39793Labels = mixedMoment B raw39793step0 raw39793step0Labels := by
      have ha : raw39793step0 = (fun i j => raw39793 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39793step0 raw39793; decide +kernel
      have hl : raw39793step0Labels = raw39793Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39793 raw39793Labels permutation157 permutation2
    _ = mixedMoment B node497 node497Labels := by rfl

def raw39794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39794Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39794step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39794step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39794step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39794 raw39794Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39794 raw39794Labels = mixedMoment B raw39794step0 raw39794step0Labels := by
      have hz : ∀ j, raw39794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39794step0 = (fun i j => raw39794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39794step0 raw39794; decide +kernel
      have hl : raw39794step0Labels = raw39794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39794 raw39794Labels permutation434 hz
    mixedMoment B raw39794step0 raw39794step0Labels = mixedMoment B raw39794step1 raw39794step1Labels := by
      have hz : ∀ j, raw39794step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39794step1 = (fun i j => raw39794step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39794step1 raw39794step0; decide +kernel
      have hl : raw39794step1Labels = raw39794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39794step0 raw39794step0Labels permutation80 hz
    mixedMoment B raw39794step1 raw39794step1Labels = mixedMoment B raw39794step2 raw39794step2Labels := by
      have ha : raw39794step2 = (fun i j => raw39794step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39794step2 raw39794step1; decide +kernel
      have hl : raw39794step2Labels = raw39794step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39794step1 raw39794step1Labels permutation27 permutation5
    _ = mixedMoment B node410 node410Labels := by rfl

def raw39795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39795Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39795step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39795step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39795 raw39795Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw39795 raw39795Labels = mixedMoment B raw39795step0 raw39795step0Labels := by
      have hz : ∀ j, raw39795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39795step0 = (fun i j => raw39795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39795step0 raw39795; decide +kernel
      have hl : raw39795step0Labels = raw39795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39795 raw39795Labels permutation434 hz
    mixedMoment B raw39795step0 raw39795step0Labels = mixedMoment B raw39795step1 raw39795step1Labels := by
      have hz : ∀ j, raw39795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39795step1 = (fun i j => raw39795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39795step1 raw39795step0; decide +kernel
      have hl : raw39795step1Labels = raw39795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39795step0 raw39795step0Labels permutation80 hz
    _ = mixedMoment B node503 node503Labels := by rfl

def raw39796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39796Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39796step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39796step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39796 raw39796Labels = mixedMoment B node501 node501Labels := by
  calc
    mixedMoment B raw39796 raw39796Labels = mixedMoment B raw39796step0 raw39796step0Labels := by
      have hz : ∀ j, raw39796 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39796step0 = (fun i j => raw39796 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39796step0 raw39796; decide +kernel
      have hl : raw39796step0Labels = raw39796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39796 raw39796Labels permutation434 hz
    mixedMoment B raw39796step0 raw39796step0Labels = mixedMoment B raw39796step1 raw39796step1Labels := by
      have hz : ∀ j, raw39796step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39796step1 = (fun i j => raw39796step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39796step1 raw39796step0; decide +kernel
      have hl : raw39796step1Labels = raw39796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39796step0 raw39796step0Labels permutation80 hz
    _ = mixedMoment B node501 node501Labels := by rfl

def raw39797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39797Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39797step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![2, 1, -3]]
def raw39797step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39797step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39797 raw39797Labels = mixedMoment B node354 node354Labels := by
  calc
    mixedMoment B raw39797 raw39797Labels = mixedMoment B raw39797step0 raw39797step0Labels := by
      have hz : ∀ j, raw39797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39797step0 = (fun i j => raw39797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39797step0 raw39797; decide +kernel
      have hl : raw39797step0Labels = raw39797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39797 raw39797Labels permutation434 hz
    mixedMoment B raw39797step0 raw39797step0Labels = mixedMoment B raw39797step1 raw39797step1Labels := by
      have hz : ∀ j, raw39797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39797step1 = (fun i j => raw39797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39797step1 raw39797step0; decide +kernel
      have hl : raw39797step1Labels = raw39797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39797step0 raw39797step0Labels permutation80 hz
    mixedMoment B raw39797step1 raw39797step1Labels = mixedMoment B raw39797step2 raw39797step2Labels := by
      have ha : raw39797step2 = (fun i j => raw39797step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39797step2 raw39797step1; decide +kernel
      have hl : raw39797step2Labels = raw39797step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39797step1 raw39797step1Labels permutation29 permutation7
    _ = mixedMoment B node354 node354Labels := by rfl

def raw39798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39798Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39798step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39798step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39798 raw39798Labels = mixedMoment B node491 node491Labels := by
  calc
    mixedMoment B raw39798 raw39798Labels = mixedMoment B raw39798step0 raw39798step0Labels := by
      have hz : ∀ j, raw39798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39798step0 = (fun i j => raw39798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39798step0 raw39798; decide +kernel
      have hl : raw39798step0Labels = raw39798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39798 raw39798Labels permutation346 hz
    mixedMoment B raw39798step0 raw39798step0Labels = mixedMoment B raw39798step1 raw39798step1Labels := by
      have ha : raw39798step1 = (fun i j => raw39798step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39798step1 raw39798step0; decide +kernel
      have hl : raw39798step1Labels = raw39798step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39798step0 raw39798step0Labels permutation141 permutation5
    _ = mixedMoment B node491 node491Labels := by rfl

def raw39799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39799Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39799step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw39799step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39799step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39799 raw39799Labels = mixedMoment B node487 node487Labels := by
  calc
    mixedMoment B raw39799 raw39799Labels = mixedMoment B raw39799step0 raw39799step0Labels := by
      have hz : ∀ j, raw39799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39799step0 = (fun i j => raw39799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39799step0 raw39799; decide +kernel
      have hl : raw39799step0Labels = raw39799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39799 raw39799Labels permutation346 hz
    mixedMoment B raw39799step0 raw39799step0Labels = mixedMoment B raw39799step1 raw39799step1Labels := by
      have ha : raw39799step1 = (fun i j => raw39799step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39799step1 raw39799step0; decide +kernel
      have hl : raw39799step1Labels = raw39799step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39799step0 raw39799step0Labels permutation151 permutation2
    mixedMoment B raw39799step1 raw39799step1Labels = mixedMoment B raw39799step2 raw39799step2Labels := by
      have ha : raw39799step2 = -raw39799step1 := by apply Matrix.ext; change ∀ i j, raw39799step2 i j = -(raw39799step1 i j); unfold raw39799step2 raw39799step1; decide +kernel
      have hl : raw39799step2Labels = raw39799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node487 node487Labels := by rfl

def raw39800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39800Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39800step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39800step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39800 raw39800Labels = mixedMoment B node348 node348Labels := by
  calc
    mixedMoment B raw39800 raw39800Labels = mixedMoment B raw39800step0 raw39800step0Labels := by
      have hz : ∀ j, raw39800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39800step0 = (fun i j => raw39800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39800step0 raw39800; decide +kernel
      have hl : raw39800step0Labels = raw39800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39800 raw39800Labels permutation346 hz
    mixedMoment B raw39800step0 raw39800step0Labels = mixedMoment B raw39800step1 raw39800step1Labels := by
      have ha : raw39800step1 = (fun i j => raw39800step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39800step1 raw39800step0; decide +kernel
      have hl : raw39800step1Labels = raw39800step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39800step0 raw39800step0Labels permutation139 permutation7
    _ = mixedMoment B node348 node348Labels := by rfl

def raw39801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39801Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39801step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw39801step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39801 raw39801Labels = mixedMoment B node346 node346Labels := by
  calc
    mixedMoment B raw39801 raw39801Labels = mixedMoment B raw39801step0 raw39801step0Labels := by
      have hz : ∀ j, raw39801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39801step0 = (fun i j => raw39801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39801step0 raw39801; decide +kernel
      have hl : raw39801step0Labels = raw39801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39801 raw39801Labels permutation346 hz
    mixedMoment B raw39801step0 raw39801step0Labels = mixedMoment B raw39801step1 raw39801step1Labels := by
      have ha : raw39801step1 = (fun i j => raw39801step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39801step1 raw39801step0; decide +kernel
      have hl : raw39801step1Labels = raw39801step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39801step0 raw39801step0Labels permutation139 permutation7
    _ = mixedMoment B node346 node346Labels := by rfl

def raw39802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39802Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39802step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw39802step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39802 raw39802Labels = mixedMoment B node476 node476Labels := by
  calc
    mixedMoment B raw39802 raw39802Labels = mixedMoment B raw39802step0 raw39802step0Labels := by
      have ha : raw39802step0 = (fun i j => raw39802 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39802step0 raw39802; decide +kernel
      have hl : raw39802step0Labels = raw39802Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39802 raw39802Labels permutation195 permutation7
    mixedMoment B raw39802step0 raw39802step0Labels = mixedMoment B raw39802step1 raw39802step1Labels := by
      have ha : raw39802step1 = -raw39802step0 := by apply Matrix.ext; change ∀ i j, raw39802step1 i j = -(raw39802step0 i j); unfold raw39802step1 raw39802step0; decide +kernel
      have hl : raw39802step1Labels = raw39802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node476 node476Labels := by rfl

def raw39803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39803Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39803step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39803step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39803 raw39803Labels = mixedMoment B node484 node484Labels := by
  calc
    mixedMoment B raw39803 raw39803Labels = mixedMoment B raw39803step0 raw39803step0Labels := by
      have ha : raw39803step0 = (fun i j => raw39803 (permutation192 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39803step0 raw39803; decide +kernel
      have hl : raw39803step0Labels = raw39803Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39803 raw39803Labels permutation192 permutation7
    mixedMoment B raw39803step0 raw39803step0Labels = mixedMoment B raw39803step1 raw39803step1Labels := by
      have ha : raw39803step1 = -raw39803step0 := by apply Matrix.ext; change ∀ i j, raw39803step1 i j = -(raw39803step0 i j); unfold raw39803step1 raw39803step0; decide +kernel
      have hl : raw39803step1Labels = raw39803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node484 node484Labels := by rfl

def raw39804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39804Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw39804step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw39804step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39804step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39804step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39804step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39804 raw39804Labels = mixedMoment B node269 node269Labels := by
  calc
    mixedMoment B raw39804 raw39804Labels = mixedMoment B raw39804step0 raw39804step0Labels := by
      have hz : ∀ j, raw39804 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39804step0 = (fun i j => raw39804 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39804step0 raw39804; decide +kernel
      have hl : raw39804step0Labels = raw39804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39804 raw39804Labels permutation520 hz
    mixedMoment B raw39804step0 raw39804step0Labels = mixedMoment B raw39804step1 raw39804step1Labels := by
      have hz : ∀ j, raw39804step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39804step1 = (fun i j => raw39804step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39804step1 raw39804step0; decide +kernel
      have hl : raw39804step1Labels = raw39804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39804step0 raw39804step0Labels permutation104 hz
    mixedMoment B raw39804step1 raw39804step1Labels = mixedMoment B raw39804step2 raw39804step2Labels := by
      have ha : raw39804step2 = (fun i j => raw39804step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39804step2 raw39804step1; decide +kernel
      have hl : raw39804step2Labels = raw39804step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39804step1 raw39804step1Labels permutation31 permutation3
    mixedMoment B raw39804step2 raw39804step2Labels = mixedMoment B raw39804step3 raw39804step3Labels := by
      have ha : raw39804step3 = -raw39804step2 := by apply Matrix.ext; change ∀ i j, raw39804step3 i j = -(raw39804step2 i j); unfold raw39804step3 raw39804step2; decide +kernel
      have hl : raw39804step3Labels = raw39804step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node269 node269Labels := by rfl

def raw39805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39805Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw39805step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39805step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39805 raw39805Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39805 raw39805Labels = mixedMoment B raw39805step0 raw39805step0Labels := by
      have hz : ∀ j, raw39805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39805step0 = (fun i j => raw39805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39805step0 raw39805; decide +kernel
      have hl : raw39805step0Labels = raw39805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39805 raw39805Labels permutation434 hz
    mixedMoment B raw39805step0 raw39805step0Labels = mixedMoment B raw39805step1 raw39805step1Labels := by
      have ha : raw39805step1 = (fun i j => raw39805step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39805step1 raw39805step0; decide +kernel
      have hl : raw39805step1Labels = raw39805step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39805step0 raw39805step0Labels permutation146 permutation5
    _ = mixedMoment B node384 node384Labels := by rfl

def raw39806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39806Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39806step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39806step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39806step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39806 raw39806Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw39806 raw39806Labels = mixedMoment B raw39806step0 raw39806step0Labels := by
      have hz : ∀ j, raw39806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39806step0 = (fun i j => raw39806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39806step0 raw39806; decide +kernel
      have hl : raw39806step0Labels = raw39806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39806 raw39806Labels permutation434 hz
    mixedMoment B raw39806step0 raw39806step0Labels = mixedMoment B raw39806step1 raw39806step1Labels := by
      have ha : raw39806step1 = (fun i j => raw39806step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39806step1 raw39806step0; decide +kernel
      have hl : raw39806step1Labels = raw39806step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39806step0 raw39806step0Labels permutation151 permutation3
    mixedMoment B raw39806step1 raw39806step1Labels = mixedMoment B raw39806step2 raw39806step2Labels := by
      have ha : raw39806step2 = -raw39806step1 := by apply Matrix.ext; change ∀ i j, raw39806step2 i j = -(raw39806step1 i j); unfold raw39806step2 raw39806step1; decide +kernel
      have hl : raw39806step2Labels = raw39806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node468 node468Labels := by rfl

def raw39807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39807Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39807step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39807 raw39807Labels = mixedMoment B node491 node491Labels := by
  calc
    mixedMoment B raw39807 raw39807Labels = mixedMoment B raw39807step0 raw39807step0Labels := by
      have hz : ∀ j, raw39807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39807step0 = (fun i j => raw39807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39807step0 raw39807; decide +kernel
      have hl : raw39807step0Labels = raw39807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39807 raw39807Labels permutation434 hz
    _ = mixedMoment B node491 node491Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
