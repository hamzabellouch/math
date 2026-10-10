import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw29440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29440 raw29440Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw29440 raw29440Labels = mixedMoment B raw29440step0 raw29440step0Labels := by
      have hz : ∀ j, raw29440 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29440step0 = (fun i j => raw29440 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29440step0 raw29440; decide +kernel
      have hl : raw29440step0Labels = raw29440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29440 raw29440Labels permutation434 hz
    mixedMoment B raw29440step0 raw29440step0Labels = mixedMoment B raw29440step1 raw29440step1Labels := by
      have ha : raw29440step1 = (fun i j => raw29440step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29440step1 raw29440step0; decide +kernel
      have hl : raw29440step1Labels = raw29440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29440step0 raw29440step0Labels permutation33 permutation2
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw29441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29441 raw29441Labels = mixedMoment B node2902 node2902Labels := by
  calc
    mixedMoment B raw29441 raw29441Labels = mixedMoment B raw29441step0 raw29441step0Labels := by
      have ha : raw29441step0 = (fun i j => raw29441 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29441step0 raw29441; decide +kernel
      have hl : raw29441step0Labels = raw29441Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29441 raw29441Labels permutation159 permutation2
    _ = mixedMoment B node2902 node2902Labels := by rfl

def raw29442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw29442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw29442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29442 raw29442Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw29442 raw29442Labels = mixedMoment B raw29442step0 raw29442step0Labels := by
      have hz : ∀ j, raw29442 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29442step0 = (fun i j => raw29442 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29442step0 raw29442; decide +kernel
      have hl : raw29442step0Labels = raw29442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29442 raw29442Labels permutation434 hz
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw29443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw29443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, -2, 1]]
def raw29443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29443 raw29443Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw29443 raw29443Labels = mixedMoment B raw29443step0 raw29443step0Labels := by
      have hz : ∀ j, raw29443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29443step0 = (fun i j => raw29443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29443step0 raw29443; decide +kernel
      have hl : raw29443step0Labels = raw29443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29443 raw29443Labels permutation434 hz
    mixedMoment B raw29443step0 raw29443step0Labels = mixedMoment B raw29443step1 raw29443step1Labels := by
      have ha : raw29443step1 = (fun i j => raw29443step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29443step1 raw29443step0; decide +kernel
      have hl : raw29443step1Labels = raw29443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29443step0 raw29443step0Labels permutation36 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw29444 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2], ![-1, 1]]
def raw29444Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29444step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![-1, 1]]
def raw29444step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29444step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw29444step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29444step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw29444step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29444 raw29444Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw29444 raw29444Labels = mixedMoment B raw29444step0 raw29444step0Labels := by
      have hz : ∀ j, raw29444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29444step0 = (fun i j => raw29444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29444step0 raw29444; decide +kernel
      have hl : raw29444step0Labels = raw29444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29444 raw29444Labels permutation434 hz
    mixedMoment B raw29444step0 raw29444step0Labels = mixedMoment B raw29444step1 raw29444step1Labels := by
      have ha : raw29444step1 = (fun i j => raw29444step0 (permutation116 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29444step1 raw29444step0; decide +kernel
      have hl : raw29444step1Labels = raw29444step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29444step0 raw29444step0Labels permutation116 permutation0
    mixedMoment B raw29444step1 raw29444step1Labels = mixedMoment B raw29444step2 raw29444step2Labels := by
      have ha : raw29444step2 = -raw29444step1 := by apply Matrix.ext; change ∀ i j, raw29444step2 i j = -(raw29444step1 i j); unfold raw29444step2 raw29444step1; decide +kernel
      have hl : raw29444step2Labels = raw29444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw29445 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29445 raw29445Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw29445 raw29445Labels = mixedMoment B raw29445step0 raw29445step0Labels := by
      have hz : ∀ j, raw29445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29445step0 = (fun i j => raw29445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29445step0 raw29445; decide +kernel
      have hl : raw29445step0Labels = raw29445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29445 raw29445Labels permutation434 hz
    mixedMoment B raw29445step0 raw29445step0Labels = mixedMoment B raw29445step1 raw29445step1Labels := by
      have ha : raw29445step1 = (fun i j => raw29445step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29445step1 raw29445step0; decide +kernel
      have hl : raw29445step1Labels = raw29445step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29445step0 raw29445step0Labels permutation149 permutation4
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw29446 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29446 raw29446Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw29446 raw29446Labels = mixedMoment B raw29446step0 raw29446step0Labels := by
      have hz : ∀ j, raw29446 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29446step0 = (fun i j => raw29446 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29446step0 raw29446; decide +kernel
      have hl : raw29446step0Labels = raw29446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29446 raw29446Labels permutation434 hz
    mixedMoment B raw29446step0 raw29446step0Labels = mixedMoment B raw29446step1 raw29446step1Labels := by
      have ha : raw29446step1 = (fun i j => raw29446step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29446step1 raw29446step0; decide +kernel
      have hl : raw29446step1Labels = raw29446step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29446step0 raw29446step0Labels permutation151 permutation4
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw29447 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw29447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29447 raw29447Labels = mixedMoment B node2674 node2674Labels := by
  calc
    mixedMoment B raw29447 raw29447Labels = mixedMoment B raw29447step0 raw29447step0Labels := by
      have hz : ∀ j, raw29447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29447step0 = (fun i j => raw29447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29447step0 raw29447; decide +kernel
      have hl : raw29447step0Labels = raw29447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29447 raw29447Labels permutation434 hz
    mixedMoment B raw29447step0 raw29447step0Labels = mixedMoment B raw29447step1 raw29447step1Labels := by
      have ha : raw29447step1 = (fun i j => raw29447step0 (permutation148 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29447step1 raw29447step0; decide +kernel
      have hl : raw29447step1Labels = raw29447step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29447step0 raw29447step0Labels permutation148 permutation4
    _ = mixedMoment B node2674 node2674Labels := by rfl

def raw29448 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw29448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29448 raw29448Labels = mixedMoment B node2668 node2668Labels := by
  calc
    mixedMoment B raw29448 raw29448Labels = mixedMoment B raw29448step0 raw29448step0Labels := by
      have ha : raw29448step0 = (fun i j => raw29448 (permutation674 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29448step0 raw29448; decide +kernel
      have hl : raw29448step0Labels = raw29448Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29448 raw29448Labels permutation674 permutation4
    _ = mixedMoment B node2668 node2668Labels := by rfl

def raw29449 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw29449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29449 raw29449Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw29449 raw29449Labels = mixedMoment B raw29449step0 raw29449step0Labels := by
      have hz : ∀ j, raw29449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29449step0 = (fun i j => raw29449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29449step0 raw29449; decide +kernel
      have hl : raw29449step0Labels = raw29449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29449 raw29449Labels permutation434 hz
    mixedMoment B raw29449step0 raw29449step0Labels = mixedMoment B raw29449step1 raw29449step1Labels := by
      have ha : raw29449step1 = (fun i j => raw29449step0 (permutation121 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29449step1 raw29449step0; decide +kernel
      have hl : raw29449step1Labels = raw29449step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29449step0 raw29449step0Labels permutation121 permutation2
    _ = mixedMoment B node2584 node2584Labels := by rfl

def raw29450 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29450 raw29450Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw29450 raw29450Labels = mixedMoment B raw29450step0 raw29450step0Labels := by
      have hz : ∀ j, raw29450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29450step0 = (fun i j => raw29450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29450step0 raw29450; decide +kernel
      have hl : raw29450step0Labels = raw29450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29450 raw29450Labels permutation434 hz
    mixedMoment B raw29450step0 raw29450step0Labels = mixedMoment B raw29450step1 raw29450step1Labels := by
      have ha : raw29450step1 = (fun i j => raw29450step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29450step1 raw29450step0; decide +kernel
      have hl : raw29450step1Labels = raw29450step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29450step0 raw29450step0Labels permutation36 permutation2
    mixedMoment B raw29450step1 raw29450step1Labels = mixedMoment B raw29450step2 raw29450step2Labels := by
      have ha : raw29450step2 = -raw29450step1 := by apply Matrix.ext; change ∀ i j, raw29450step2 i j = -(raw29450step1 i j); unfold raw29450step2 raw29450step1; decide +kernel
      have hl : raw29450step2Labels = raw29450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw29451 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw29451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw29451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29451 raw29451Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw29451 raw29451Labels = mixedMoment B raw29451step0 raw29451step0Labels := by
      have hz : ∀ j, raw29451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29451step0 = (fun i j => raw29451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29451step0 raw29451; decide +kernel
      have hl : raw29451step0Labels = raw29451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29451 raw29451Labels permutation434 hz
    mixedMoment B raw29451step0 raw29451step0Labels = mixedMoment B raw29451step1 raw29451step1Labels := by
      have ha : raw29451step1 = (fun i j => raw29451step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29451step1 raw29451step0; decide +kernel
      have hl : raw29451step1Labels = raw29451step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29451step0 raw29451step0Labels permutation40 permutation4
    mixedMoment B raw29451step1 raw29451step1Labels = mixedMoment B raw29451step2 raw29451step2Labels := by
      have ha : raw29451step2 = -raw29451step1 := by apply Matrix.ext; change ∀ i j, raw29451step2 i j = -(raw29451step1 i j); unfold raw29451step2 raw29451step1; decide +kernel
      have hl : raw29451step2Labels = raw29451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw29452 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw29452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw29452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29452 raw29452Labels = mixedMoment B node3614 node3614Labels := by
  calc
    mixedMoment B raw29452 raw29452Labels = mixedMoment B raw29452step0 raw29452step0Labels := by
      have hz : ∀ j, raw29452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29452step0 = (fun i j => raw29452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29452step0 raw29452; decide +kernel
      have hl : raw29452step0Labels = raw29452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29452 raw29452Labels permutation434 hz
    mixedMoment B raw29452step0 raw29452step0Labels = mixedMoment B raw29452step1 raw29452step1Labels := by
      have hz : ∀ j, raw29452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29452step1 = (fun i j => raw29452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29452step1 raw29452step0; decide +kernel
      have hl : raw29452step1Labels = raw29452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29452step0 raw29452step0Labels permutation80 hz
    mixedMoment B raw29452step1 raw29452step1Labels = mixedMoment B raw29452step2 raw29452step2Labels := by
      have ha : raw29452step2 = (fun i j => raw29452step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29452step2 raw29452step1; decide +kernel
      have hl : raw29452step2Labels = raw29452step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29452step1 raw29452step1Labels permutation8 permutation4
    mixedMoment B raw29452step2 raw29452step2Labels = mixedMoment B raw29452step3 raw29452step3Labels := by
      have ha : raw29452step3 = -raw29452step2 := by apply Matrix.ext; change ∀ i j, raw29452step3 i j = -(raw29452step2 i j); unfold raw29452step3 raw29452step2; decide +kernel
      have hl : raw29452step3Labels = raw29452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3614 node3614Labels := by rfl

def raw29453 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29453 raw29453Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw29453 raw29453Labels = mixedMoment B raw29453step0 raw29453step0Labels := by
      have ha : raw29453step0 = (fun i j => raw29453 (permutation178 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29453step0 raw29453; decide +kernel
      have hl : raw29453step0Labels = raw29453Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29453 raw29453Labels permutation178 permutation4
    mixedMoment B raw29453step0 raw29453step0Labels = mixedMoment B raw29453step1 raw29453step1Labels := by
      have ha : raw29453step1 = -raw29453step0 := by apply Matrix.ext; change ∀ i j, raw29453step1 i j = -(raw29453step0 i j); unfold raw29453step1 raw29453step0; decide +kernel
      have hl : raw29453step1Labels = raw29453step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw29454 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29454 raw29454Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29454 raw29454Labels = mixedMoment B raw29454step0 raw29454step0Labels := by
      have hz : ∀ j, raw29454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29454step0 = (fun i j => raw29454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29454step0 raw29454; decide +kernel
      have hl : raw29454step0Labels = raw29454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29454 raw29454Labels permutation434 hz
    mixedMoment B raw29454step0 raw29454step0Labels = mixedMoment B raw29454step1 raw29454step1Labels := by
      have ha : raw29454step1 = (fun i j => raw29454step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29454step1 raw29454step0; decide +kernel
      have hl : raw29454step1Labels = raw29454step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29454step0 raw29454step0Labels permutation38 permutation4
    mixedMoment B raw29454step1 raw29454step1Labels = mixedMoment B raw29454step2 raw29454step2Labels := by
      have ha : raw29454step2 = -raw29454step1 := by apply Matrix.ext; change ∀ i j, raw29454step2 i j = -(raw29454step1 i j); unfold raw29454step2 raw29454step1; decide +kernel
      have hl : raw29454step2Labels = raw29454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw29455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29455 raw29455Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw29455 raw29455Labels = mixedMoment B raw29455step0 raw29455step0Labels := by
      have ha : raw29455step0 = (fun i j => raw29455 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29455step0 raw29455; decide +kernel
      have hl : raw29455step0Labels = raw29455Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29455 raw29455Labels permutation686 permutation2
    mixedMoment B raw29455step0 raw29455step0Labels = mixedMoment B raw29455step1 raw29455step1Labels := by
      have ha : raw29455step1 = -raw29455step0 := by apply Matrix.ext; change ∀ i j, raw29455step1 i j = -(raw29455step0 i j); unfold raw29455step1 raw29455step0; decide +kernel
      have hl : raw29455step1Labels = raw29455step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw29456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29456 raw29456Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw29456 raw29456Labels = mixedMoment B raw29456step0 raw29456step0Labels := by
      have hz : ∀ j, raw29456 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw29456step0 = (fun i j => raw29456 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw29456step0 raw29456; decide +kernel
      have hl : raw29456step0Labels = raw29456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29456 raw29456Labels permutation265 hz
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw29457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29457 raw29457Labels = mixedMoment B node2545 node2545Labels := by
  calc
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw29458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29458 raw29458Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw29458 raw29458Labels = mixedMoment B raw29458step0 raw29458step0Labels := by
      have ha : raw29458step0 = (fun i j => raw29458 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29458step0 raw29458; decide +kernel
      have hl : raw29458step0Labels = raw29458Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29458 raw29458Labels permutation176 permutation2
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw29459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw29459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29459 raw29459Labels = mixedMoment B node2423 node2423Labels := by
  calc
    mixedMoment B raw29459 raw29459Labels = mixedMoment B raw29459step0 raw29459step0Labels := by
      have ha : raw29459step0 = (fun i j => raw29459 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29459step0 raw29459; decide +kernel
      have hl : raw29459step0Labels = raw29459Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29459 raw29459Labels permutation177 permutation2
    _ = mixedMoment B node2423 node2423Labels := by rfl

def raw29460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29460 raw29460Labels = mixedMoment B node2350 node2350Labels := by
  calc
    _ = mixedMoment B node2350 node2350Labels := by rfl

def raw29461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw29461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29461 raw29461Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw29461 raw29461Labels = mixedMoment B raw29461step0 raw29461step0Labels := by
      have ha : raw29461step0 = (fun i j => raw29461 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29461step0 raw29461; decide +kernel
      have hl : raw29461step0Labels = raw29461Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29461 raw29461Labels permutation153 permutation2
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw29462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29462 raw29462Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw29462 raw29462Labels = mixedMoment B raw29462step0 raw29462step0Labels := by
      have ha : raw29462step0 = (fun i j => raw29462 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29462step0 raw29462; decide +kernel
      have hl : raw29462step0Labels = raw29462Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29462 raw29462Labels permutation159 permutation2
    _ = mixedMoment B node1330 node1330Labels := by rfl

def raw29463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29463 raw29463Labels = mixedMoment B node2824 node2824Labels := by
  calc
    mixedMoment B raw29463 raw29463Labels = mixedMoment B raw29463step0 raw29463step0Labels := by
      have ha : raw29463step0 = (fun i j => raw29463 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29463step0 raw29463; decide +kernel
      have hl : raw29463step0Labels = raw29463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29463 raw29463Labels permutation159 permutation2
    _ = mixedMoment B node2824 node2824Labels := by rfl

def raw29464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29464 raw29464Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw29464 raw29464Labels = mixedMoment B raw29464step0 raw29464step0Labels := by
      have ha : raw29464step0 = (fun i j => raw29464 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29464step0 raw29464; decide +kernel
      have hl : raw29464step0Labels = raw29464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29464 raw29464Labels permutation159 permutation2
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw29465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29465 raw29465Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw29465 raw29465Labels = mixedMoment B raw29465step0 raw29465step0Labels := by
      have ha : raw29465step0 = (fun i j => raw29465 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29465step0 raw29465; decide +kernel
      have hl : raw29465step0Labels = raw29465Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29465 raw29465Labels permutation159 permutation2
    _ = mixedMoment B node2896 node2896Labels := by rfl

def raw29466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw29466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29466 raw29466Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw29466 raw29466Labels = mixedMoment B raw29466step0 raw29466step0Labels := by
      have ha : raw29466step0 = (fun i j => raw29466 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29466step0 raw29466; decide +kernel
      have hl : raw29466step0Labels = raw29466Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29466 raw29466Labels permutation158 permutation2
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw29467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw29467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29467 raw29467Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw29467 raw29467Labels = mixedMoment B raw29467step0 raw29467step0Labels := by
      have ha : raw29467step0 = (fun i j => raw29467 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29467step0 raw29467; decide +kernel
      have hl : raw29467step0Labels = raw29467Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29467 raw29467Labels permutation162 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw29468 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2], ![0, 0]]
def raw29468Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29468step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw29468step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29468step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw29468step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29468step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw29468step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29468 raw29468Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw29468 raw29468Labels = mixedMoment B raw29468step0 raw29468step0Labels := by
      have hz : ∀ j, raw29468 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw29468step0 = (fun i j => raw29468 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw29468step0 raw29468; decide +kernel
      have hl : raw29468step0Labels = raw29468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29468 raw29468Labels permutation590 hz
    mixedMoment B raw29468step0 raw29468step0Labels = mixedMoment B raw29468step1 raw29468step1Labels := by
      have ha : raw29468step1 = (fun i j => raw29468step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29468step1 raw29468step0; decide +kernel
      have hl : raw29468step1Labels = raw29468step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29468step0 raw29468step0Labels permutation140 permutation0
    mixedMoment B raw29468step1 raw29468step1Labels = mixedMoment B raw29468step2 raw29468step2Labels := by
      have ha : raw29468step2 = -raw29468step1 := by apply Matrix.ext; change ∀ i j, raw29468step2 i j = -(raw29468step1 i j); unfold raw29468step2 raw29468step1; decide +kernel
      have hl : raw29468step2Labels = raw29468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw29469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29469 raw29469Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw29469 raw29469Labels = mixedMoment B raw29469step0 raw29469step0Labels := by
      have ha : raw29469step0 = (fun i j => raw29469 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29469step0 raw29469; decide +kernel
      have hl : raw29469step0Labels = raw29469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29469 raw29469Labels permutation582 permutation2
    mixedMoment B raw29469step0 raw29469step0Labels = mixedMoment B raw29469step1 raw29469step1Labels := by
      have ha : raw29469step1 = -raw29469step0 := by apply Matrix.ext; change ∀ i j, raw29469step1 i j = -(raw29469step0 i j); unfold raw29469step1 raw29469step0; decide +kernel
      have hl : raw29469step1Labels = raw29469step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw29470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29470 raw29470Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw29470 raw29470Labels = mixedMoment B raw29470step0 raw29470step0Labels := by
      have ha : raw29470step0 = (fun i j => raw29470 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29470step0 raw29470; decide +kernel
      have hl : raw29470step0Labels = raw29470Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29470 raw29470Labels permutation201 permutation2
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw29471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29471 raw29471Labels = mixedMoment B node2349 node2349Labels := by
  calc
    mixedMoment B raw29471 raw29471Labels = mixedMoment B raw29471step0 raw29471step0Labels := by
      have ha : raw29471step0 = (fun i j => raw29471 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29471step0 raw29471; decide +kernel
      have hl : raw29471step0Labels = raw29471Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29471 raw29471Labels permutation582 permutation2
    mixedMoment B raw29471step0 raw29471step0Labels = mixedMoment B raw29471step1 raw29471step1Labels := by
      have ha : raw29471step1 = -raw29471step0 := by apply Matrix.ext; change ∀ i j, raw29471step1 i j = -(raw29471step0 i j); unfold raw29471step1 raw29471step0; decide +kernel
      have hl : raw29471step1Labels = raw29471step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2349 node2349Labels := by rfl

def raw29472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw29472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29472 raw29472Labels = mixedMoment B node2890 node2890Labels := by
  calc
    mixedMoment B raw29472 raw29472Labels = mixedMoment B raw29472step0 raw29472step0Labels := by
      have ha : raw29472step0 = (fun i j => raw29472 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29472step0 raw29472; decide +kernel
      have hl : raw29472step0Labels = raw29472Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29472 raw29472Labels permutation158 permutation2
    _ = mixedMoment B node2890 node2890Labels := by rfl

def raw29473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29473 raw29473Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw29473 raw29473Labels = mixedMoment B raw29473step0 raw29473step0Labels := by
      have ha : raw29473step0 = (fun i j => raw29473 (permutation204 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29473step0 raw29473; decide +kernel
      have hl : raw29473step0Labels = raw29473Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29473 raw29473Labels permutation204 permutation2
    mixedMoment B raw29473step0 raw29473step0Labels = mixedMoment B raw29473step1 raw29473step1Labels := by
      have ha : raw29473step1 = -raw29473step0 := by apply Matrix.ext; change ∀ i j, raw29473step1 i j = -(raw29473step0 i j); unfold raw29473step1 raw29473step0; decide +kernel
      have hl : raw29473step1Labels = raw29473step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw29474 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29474 raw29474Labels = mixedMoment B node3430 node3430Labels := by
  calc
    mixedMoment B raw29474 raw29474Labels = mixedMoment B raw29474step0 raw29474step0Labels := by
      have ha : raw29474step0 = (fun i j => raw29474 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29474step0 raw29474; decide +kernel
      have hl : raw29474step0Labels = raw29474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29474 raw29474Labels permutation162 permutation2
    mixedMoment B raw29474step0 raw29474step0Labels = mixedMoment B raw29474step1 raw29474step1Labels := by
      have ha : raw29474step1 = -raw29474step0 := by apply Matrix.ext; change ∀ i j, raw29474step1 i j = -(raw29474step0 i j); unfold raw29474step1 raw29474step0; decide +kernel
      have hl : raw29474step1Labels = raw29474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3430 node3430Labels := by rfl

def raw29475 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29475 raw29475Labels = mixedMoment B node2534 node2534Labels := by
  calc
    mixedMoment B raw29475 raw29475Labels = mixedMoment B raw29475step0 raw29475step0Labels := by
      have ha : raw29475step0 = (fun i j => raw29475 (permutation552 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29475step0 raw29475; decide +kernel
      have hl : raw29475step0Labels = raw29475Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29475 raw29475Labels permutation552 permutation2
    _ = mixedMoment B node2534 node2534Labels := by rfl

def raw29476 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29476 raw29476Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw29476 raw29476Labels = mixedMoment B raw29476step0 raw29476step0Labels := by
      have ha : raw29476step0 = (fun i j => raw29476 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29476step0 raw29476; decide +kernel
      have hl : raw29476step0Labels = raw29476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29476 raw29476Labels permutation159 permutation2
    mixedMoment B raw29476step0 raw29476step0Labels = mixedMoment B raw29476step1 raw29476step1Labels := by
      have ha : raw29476step1 = -raw29476step0 := by apply Matrix.ext; change ∀ i j, raw29476step1 i j = -(raw29476step0 i j); unfold raw29476step1 raw29476step0; decide +kernel
      have hl : raw29476step1Labels = raw29476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3433 node3433Labels := by rfl

def raw29477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29477 raw29477Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw29477 raw29477Labels = mixedMoment B raw29477step0 raw29477step0Labels := by
      have ha : raw29477step0 = (fun i j => raw29477 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29477step0 raw29477; decide +kernel
      have hl : raw29477step0Labels = raw29477Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29477 raw29477Labels permutation176 permutation4
    mixedMoment B raw29477step0 raw29477step0Labels = mixedMoment B raw29477step1 raw29477step1Labels := by
      have ha : raw29477step1 = -raw29477step0 := by apply Matrix.ext; change ∀ i j, raw29477step1 i j = -(raw29477step0 i j); unfold raw29477step1 raw29477step0; decide +kernel
      have hl : raw29477step1Labels = raw29477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1997 node1997Labels := by rfl

def raw29478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29478 raw29478Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw29478 raw29478Labels = mixedMoment B raw29478step0 raw29478step0Labels := by
      have ha : raw29478step0 = (fun i j => raw29478 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29478step0 raw29478; decide +kernel
      have hl : raw29478step0Labels = raw29478Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29478 raw29478Labels permutation152 permutation4
    mixedMoment B raw29478step0 raw29478step0Labels = mixedMoment B raw29478step1 raw29478step1Labels := by
      have ha : raw29478step1 = -raw29478step0 := by apply Matrix.ext; change ∀ i j, raw29478step1 i j = -(raw29478step0 i j); unfold raw29478step1 raw29478step0; decide +kernel
      have hl : raw29478step1Labels = raw29478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3433 node3433Labels := by rfl

def raw29479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29479 raw29479Labels = mixedMoment B node3369 node3369Labels := by
  calc
    mixedMoment B raw29479 raw29479Labels = mixedMoment B raw29479step0 raw29479step0Labels := by
      have ha : raw29479step0 = (fun i j => raw29479 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29479step0 raw29479; decide +kernel
      have hl : raw29479step0Labels = raw29479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29479 raw29479Labels permutation176 permutation4
    mixedMoment B raw29479step0 raw29479step0Labels = mixedMoment B raw29479step1 raw29479step1Labels := by
      have ha : raw29479step1 = -raw29479step0 := by apply Matrix.ext; change ∀ i j, raw29479step1 i j = -(raw29479step0 i j); unfold raw29479step1 raw29479step0; decide +kernel
      have hl : raw29479step1Labels = raw29479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3369 node3369Labels := by rfl

def raw29480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29480 raw29480Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw29480 raw29480Labels = mixedMoment B raw29480step0 raw29480step0Labels := by
      have ha : raw29480step0 = (fun i j => raw29480 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29480step0 raw29480; decide +kernel
      have hl : raw29480step0Labels = raw29480Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29480 raw29480Labels permutation176 permutation4
    mixedMoment B raw29480step0 raw29480step0Labels = mixedMoment B raw29480step1 raw29480step1Labels := by
      have ha : raw29480step1 = -raw29480step0 := by apply Matrix.ext; change ∀ i j, raw29480step1 i j = -(raw29480step0 i j); unfold raw29480step1 raw29480step0; decide +kernel
      have hl : raw29480step1Labels = raw29480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3520 node3520Labels := by rfl

def raw29481 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29481 raw29481Labels = mixedMoment B node3518 node3518Labels := by
  calc
    mixedMoment B raw29481 raw29481Labels = mixedMoment B raw29481step0 raw29481step0Labels := by
      have ha : raw29481step0 = (fun i j => raw29481 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29481step0 raw29481; decide +kernel
      have hl : raw29481step0Labels = raw29481Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29481 raw29481Labels permutation179 permutation4
    mixedMoment B raw29481step0 raw29481step0Labels = mixedMoment B raw29481step1 raw29481step1Labels := by
      have ha : raw29481step1 = -raw29481step0 := by apply Matrix.ext; change ∀ i j, raw29481step1 i j = -(raw29481step0 i j); unfold raw29481step1 raw29481step0; decide +kernel
      have hl : raw29481step1Labels = raw29481step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3518 node3518Labels := by rfl

def raw29482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29482 raw29482Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw29482 raw29482Labels = mixedMoment B raw29482step0 raw29482step0Labels := by
      have ha : raw29482step0 = (fun i j => raw29482 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29482step0 raw29482; decide +kernel
      have hl : raw29482step0Labels = raw29482Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29482 raw29482Labels permutation176 permutation2
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw29483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29483 raw29483Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw29483 raw29483Labels = mixedMoment B raw29483step0 raw29483step0Labels := by
      have hz : ∀ j, raw29483 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw29483step0 = (fun i j => raw29483 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw29483step0 raw29483; decide +kernel
      have hl : raw29483step0Labels = raw29483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29483 raw29483Labels permutation265 hz
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw29484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29484 raw29484Labels = mixedMoment B node2546 node2546Labels := by
  calc
    _ = mixedMoment B node2546 node2546Labels := by rfl

def raw29485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29485 raw29485Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw29485 raw29485Labels = mixedMoment B raw29485step0 raw29485step0Labels := by
      have ha : raw29485step0 = (fun i j => raw29485 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29485step0 raw29485; decide +kernel
      have hl : raw29485step0Labels = raw29485Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29485 raw29485Labels permutation176 permutation2
    _ = mixedMoment B node2432 node2432Labels := by rfl

def raw29486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw29486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29486 raw29486Labels = mixedMoment B node2422 node2422Labels := by
  calc
    mixedMoment B raw29486 raw29486Labels = mixedMoment B raw29486step0 raw29486step0Labels := by
      have ha : raw29486step0 = (fun i j => raw29486 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29486step0 raw29486; decide +kernel
      have hl : raw29486step0Labels = raw29486Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29486 raw29486Labels permutation177 permutation2
    _ = mixedMoment B node2422 node2422Labels := by rfl

def raw29487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29487 raw29487Labels = mixedMoment B node2351 node2351Labels := by
  calc
    _ = mixedMoment B node2351 node2351Labels := by rfl

def raw29488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw29488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29488 raw29488Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw29488 raw29488Labels = mixedMoment B raw29488step0 raw29488step0Labels := by
      have ha : raw29488step0 = (fun i j => raw29488 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29488step0 raw29488; decide +kernel
      have hl : raw29488step0Labels = raw29488Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29488 raw29488Labels permutation153 permutation2
    _ = mixedMoment B node2556 node2556Labels := by rfl

def raw29489 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29489 raw29489Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw29489 raw29489Labels = mixedMoment B raw29489step0 raw29489step0Labels := by
      have ha : raw29489step0 = (fun i j => raw29489 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29489step0 raw29489; decide +kernel
      have hl : raw29489step0Labels = raw29489Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29489 raw29489Labels permutation200 permutation2
    mixedMoment B raw29489step0 raw29489step0Labels = mixedMoment B raw29489step1 raw29489step1Labels := by
      have ha : raw29489step1 = -raw29489step0 := by apply Matrix.ext; change ∀ i j, raw29489step1 i j = -(raw29489step0 i j); unfold raw29489step1 raw29489step0; decide +kernel
      have hl : raw29489step1Labels = raw29489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3520 node3520Labels := by rfl

def raw29490 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29490 raw29490Labels = mixedMoment B node3438 node3438Labels := by
  calc
    mixedMoment B raw29490 raw29490Labels = mixedMoment B raw29490step0 raw29490step0Labels := by
      have ha : raw29490step0 = (fun i j => raw29490 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29490step0 raw29490; decide +kernel
      have hl : raw29490step0Labels = raw29490Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29490 raw29490Labels permutation161 permutation2
    mixedMoment B raw29490step0 raw29490step0Labels = mixedMoment B raw29490step1 raw29490step1Labels := by
      have ha : raw29490step1 = -raw29490step0 := by apply Matrix.ext; change ∀ i j, raw29490step1 i j = -(raw29490step0 i j); unfold raw29490step1 raw29490step0; decide +kernel
      have hl : raw29490step1Labels = raw29490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3438 node3438Labels := by rfl

def raw29491 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29491 raw29491Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw29491 raw29491Labels = mixedMoment B raw29491step0 raw29491step0Labels := by
      have hz : ∀ j, raw29491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29491step0 = (fun i j => raw29491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29491step0 raw29491; decide +kernel
      have hl : raw29491step0Labels = raw29491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29491 raw29491Labels permutation434 hz
    mixedMoment B raw29491step0 raw29491step0Labels = mixedMoment B raw29491step1 raw29491step1Labels := by
      have ha : raw29491step1 = -raw29491step0 := by apply Matrix.ext; change ∀ i j, raw29491step1 i j = -(raw29491step0 i j); unfold raw29491step1 raw29491step0; decide +kernel
      have hl : raw29491step1Labels = raw29491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw29492 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29492 raw29492Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw29492 raw29492Labels = mixedMoment B raw29492step0 raw29492step0Labels := by
      have ha : raw29492step0 = (fun i j => raw29492 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29492step0 raw29492; decide +kernel
      have hl : raw29492step0Labels = raw29492Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29492 raw29492Labels permutation158 permutation2
    mixedMoment B raw29492step0 raw29492step0Labels = mixedMoment B raw29492step1 raw29492step1Labels := by
      have ha : raw29492step1 = -raw29492step0 := by apply Matrix.ext; change ∀ i j, raw29492step1 i j = -(raw29492step0 i j); unfold raw29492step1 raw29492step0; decide +kernel
      have hl : raw29492step1Labels = raw29492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3433 node3433Labels := by rfl

def raw29493 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29493 raw29493Labels = mixedMoment B node2044 node2044Labels := by
  calc
    mixedMoment B raw29493 raw29493Labels = mixedMoment B raw29493step0 raw29493step0Labels := by
      have ha : raw29493step0 = (fun i j => raw29493 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29493step0 raw29493; decide +kernel
      have hl : raw29493step0Labels = raw29493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29493 raw29493Labels permutation176 permutation4
    mixedMoment B raw29493step0 raw29493step0Labels = mixedMoment B raw29493step1 raw29493step1Labels := by
      have ha : raw29493step1 = -raw29493step0 := by apply Matrix.ext; change ∀ i j, raw29493step1 i j = -(raw29493step0 i j); unfold raw29493step1 raw29493step0; decide +kernel
      have hl : raw29493step1Labels = raw29493step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2044 node2044Labels := by rfl

def raw29494 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29494 raw29494Labels = mixedMoment B node2002 node2002Labels := by
  calc
    mixedMoment B raw29494 raw29494Labels = mixedMoment B raw29494step0 raw29494step0Labels := by
      have ha : raw29494step0 = (fun i j => raw29494 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29494step0 raw29494; decide +kernel
      have hl : raw29494step0Labels = raw29494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29494 raw29494Labels permutation179 permutation4
    mixedMoment B raw29494step0 raw29494step0Labels = mixedMoment B raw29494step1 raw29494step1Labels := by
      have ha : raw29494step1 = -raw29494step0 := by apply Matrix.ext; change ∀ i j, raw29494step1 i j = -(raw29494step0 i j); unfold raw29494step1 raw29494step0; decide +kernel
      have hl : raw29494step1Labels = raw29494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2002 node2002Labels := by rfl

def raw29495 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29495 raw29495Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw29495 raw29495Labels = mixedMoment B raw29495step0 raw29495step0Labels := by
      have ha : raw29495step0 = (fun i j => raw29495 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29495step0 raw29495; decide +kernel
      have hl : raw29495step0Labels = raw29495Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29495 raw29495Labels permutation177 permutation4
    mixedMoment B raw29495step0 raw29495step0Labels = mixedMoment B raw29495step1 raw29495step1Labels := by
      have ha : raw29495step1 = -raw29495step0 := by apply Matrix.ext; change ∀ i j, raw29495step1 i j = -(raw29495step0 i j); unfold raw29495step1 raw29495step0; decide +kernel
      have hl : raw29495step1Labels = raw29495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1997 node1997Labels := by rfl

def raw29496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29496 raw29496Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw29496 raw29496Labels = mixedMoment B raw29496step0 raw29496step0Labels := by
      have hz : ∀ j, raw29496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29496step0 = (fun i j => raw29496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29496step0 raw29496; decide +kernel
      have hl : raw29496step0Labels = raw29496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29496 raw29496Labels permutation434 hz
    mixedMoment B raw29496step0 raw29496step0Labels = mixedMoment B raw29496step1 raw29496step1Labels := by
      have ha : raw29496step1 = (fun i j => raw29496step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29496step1 raw29496step0; decide +kernel
      have hl : raw29496step1Labels = raw29496step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29496step0 raw29496step0Labels permutation38 permutation4
    mixedMoment B raw29496step1 raw29496step1Labels = mixedMoment B raw29496step2 raw29496step2Labels := by
      have ha : raw29496step2 = -raw29496step1 := by apply Matrix.ext; change ∀ i j, raw29496step2 i j = -(raw29496step1 i j); unfold raw29496step2 raw29496step1; decide +kernel
      have hl : raw29496step2Labels = raw29496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw29497 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29497step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29497step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29497 raw29497Labels = mixedMoment B node3616 node3616Labels := by
  calc
    mixedMoment B raw29497 raw29497Labels = mixedMoment B raw29497step0 raw29497step0Labels := by
      have hz : ∀ j, raw29497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29497step0 = (fun i j => raw29497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29497step0 raw29497; decide +kernel
      have hl : raw29497step0Labels = raw29497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29497 raw29497Labels permutation434 hz
    mixedMoment B raw29497step0 raw29497step0Labels = mixedMoment B raw29497step1 raw29497step1Labels := by
      have hz : ∀ j, raw29497step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29497step1 = (fun i j => raw29497step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29497step1 raw29497step0; decide +kernel
      have hl : raw29497step1Labels = raw29497step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29497step0 raw29497step0Labels permutation80 hz
    mixedMoment B raw29497step1 raw29497step1Labels = mixedMoment B raw29497step2 raw29497step2Labels := by
      have ha : raw29497step2 = (fun i j => raw29497step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29497step2 raw29497step1; decide +kernel
      have hl : raw29497step2Labels = raw29497step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29497step1 raw29497step1Labels permutation8 permutation4
    mixedMoment B raw29497step2 raw29497step2Labels = mixedMoment B raw29497step3 raw29497step3Labels := by
      have ha : raw29497step3 = -raw29497step2 := by apply Matrix.ext; change ∀ i j, raw29497step3 i j = -(raw29497step2 i j); unfold raw29497step3 raw29497step2; decide +kernel
      have hl : raw29497step3Labels = raw29497step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3616 node3616Labels := by rfl

def raw29498 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29498 raw29498Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29498 raw29498Labels = mixedMoment B raw29498step0 raw29498step0Labels := by
      have hz : ∀ j, raw29498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29498step0 = (fun i j => raw29498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29498step0 raw29498; decide +kernel
      have hl : raw29498step0Labels = raw29498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29498 raw29498Labels permutation434 hz
    mixedMoment B raw29498step0 raw29498step0Labels = mixedMoment B raw29498step1 raw29498step1Labels := by
      have ha : raw29498step1 = (fun i j => raw29498step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29498step1 raw29498step0; decide +kernel
      have hl : raw29498step1Labels = raw29498step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29498step0 raw29498step0Labels permutation39 permutation4
    mixedMoment B raw29498step1 raw29498step1Labels = mixedMoment B raw29498step2 raw29498step2Labels := by
      have ha : raw29498step2 = -raw29498step1 := by apply Matrix.ext; change ∀ i j, raw29498step2 i j = -(raw29498step1 i j); unfold raw29498step2 raw29498step1; decide +kernel
      have hl : raw29498step2Labels = raw29498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw29499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29499 raw29499Labels = mixedMoment B node2905 node2905Labels := by
  calc
    mixedMoment B raw29499 raw29499Labels = mixedMoment B raw29499step0 raw29499step0Labels := by
      have ha : raw29499step0 = (fun i j => raw29499 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29499step0 raw29499; decide +kernel
      have hl : raw29499step0Labels = raw29499Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29499 raw29499Labels permutation159 permutation2
    _ = mixedMoment B node2905 node2905Labels := by rfl

def raw29500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw29500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw29500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29500 raw29500Labels = mixedMoment B node3680 node3680Labels := by
  calc
    mixedMoment B raw29500 raw29500Labels = mixedMoment B raw29500step0 raw29500step0Labels := by
      have ha : raw29500step0 = (fun i j => raw29500 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29500step0 raw29500; decide +kernel
      have hl : raw29500step0Labels = raw29500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29500 raw29500Labels permutation583 permutation2
    mixedMoment B raw29500step0 raw29500step0Labels = mixedMoment B raw29500step1 raw29500step1Labels := by
      have ha : raw29500step1 = -raw29500step0 := by apply Matrix.ext; change ∀ i j, raw29500step1 i j = -(raw29500step0 i j); unfold raw29500step1 raw29500step0; decide +kernel
      have hl : raw29500step1Labels = raw29500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3680 node3680Labels := by rfl

def raw29501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw29501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29501 raw29501Labels = mixedMoment B node3696 node3696Labels := by
  calc
    mixedMoment B raw29501 raw29501Labels = mixedMoment B raw29501step0 raw29501step0Labels := by
      have ha : raw29501step0 = (fun i j => raw29501 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29501step0 raw29501; decide +kernel
      have hl : raw29501step0Labels = raw29501Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29501 raw29501Labels permutation589 permutation2
    mixedMoment B raw29501step0 raw29501step0Labels = mixedMoment B raw29501step1 raw29501step1Labels := by
      have ha : raw29501step1 = -raw29501step0 := by apply Matrix.ext; change ∀ i j, raw29501step1 i j = -(raw29501step0 i j); unfold raw29501step1 raw29501step0; decide +kernel
      have hl : raw29501step1Labels = raw29501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3696 node3696Labels := by rfl

def raw29502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw29502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw29502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29502 raw29502Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw29502 raw29502Labels = mixedMoment B raw29502step0 raw29502step0Labels := by
      have ha : raw29502step0 = (fun i j => raw29502 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29502step0 raw29502; decide +kernel
      have hl : raw29502step0Labels = raw29502Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29502 raw29502Labels permutation582 permutation2
    mixedMoment B raw29502step0 raw29502step0Labels = mixedMoment B raw29502step1 raw29502step1Labels := by
      have ha : raw29502step1 = -raw29502step0 := by apply Matrix.ext; change ∀ i j, raw29502step1 i j = -(raw29502step0 i j); unfold raw29502step1 raw29502step0; decide +kernel
      have hl : raw29502step1Labels = raw29502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3683 node3683Labels := by rfl

def raw29503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw29503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw29503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29503 raw29503Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw29503 raw29503Labels = mixedMoment B raw29503step0 raw29503step0Labels := by
      have ha : raw29503step0 = (fun i j => raw29503 (permutation508 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29503step0 raw29503; decide +kernel
      have hl : raw29503step0Labels = raw29503Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29503 raw29503Labels permutation508 permutation4
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw29504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw29504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw29504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw29504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29504 raw29504Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw29504 raw29504Labels = mixedMoment B raw29504step0 raw29504step0Labels := by
      have ha : raw29504step0 = (fun i j => raw29504 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29504step0 raw29504; decide +kernel
      have hl : raw29504step0Labels = raw29504Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29504 raw29504Labels permutation584 permutation2
    mixedMoment B raw29504step0 raw29504step0Labels = mixedMoment B raw29504step1 raw29504step1Labels := by
      have ha : raw29504step1 = -raw29504step0 := by apply Matrix.ext; change ∀ i j, raw29504step1 i j = -(raw29504step0 i j); unfold raw29504step1 raw29504step0; decide +kernel
      have hl : raw29504step1Labels = raw29504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw29505 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw29505Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29505step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29505step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29505 raw29505Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw29505 raw29505Labels = mixedMoment B raw29505step0 raw29505step0Labels := by
      have ha : raw29505step0 = (fun i j => raw29505 (permutation435 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29505step0 raw29505; decide +kernel
      have hl : raw29505step0Labels = raw29505Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29505 raw29505Labels permutation435 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw29506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29506 raw29506Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw29506 raw29506Labels = mixedMoment B raw29506step0 raw29506step0Labels := by
      have hz : ∀ j, raw29506 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29506step0 = (fun i j => raw29506 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29506step0 raw29506; decide +kernel
      have hl : raw29506step0Labels = raw29506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29506 raw29506Labels permutation434 hz
    _ = mixedMoment B node4973 node4973Labels := by rfl

def raw29507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29507 raw29507Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw29507 raw29507Labels = mixedMoment B raw29507step0 raw29507step0Labels := by
      have ha : raw29507step0 = (fun i j => raw29507 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29507step0 raw29507; decide +kernel
      have hl : raw29507step0Labels = raw29507Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29507 raw29507Labels permutation158 permutation2
    _ = mixedMoment B node5114 node5114Labels := by rfl

def raw29508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29508 raw29508Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw29508 raw29508Labels = mixedMoment B raw29508step0 raw29508step0Labels := by
      have hz : ∀ j, raw29508 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29508step0 = (fun i j => raw29508 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29508step0 raw29508; decide +kernel
      have hl : raw29508step0Labels = raw29508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29508 raw29508Labels permutation434 hz
    mixedMoment B raw29508step0 raw29508step0Labels = mixedMoment B raw29508step1 raw29508step1Labels := by
      have ha : raw29508step1 = (fun i j => raw29508step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29508step1 raw29508step0; decide +kernel
      have hl : raw29508step1Labels = raw29508step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29508step0 raw29508step0Labels permutation33 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw29509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29509 raw29509Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw29509 raw29509Labels = mixedMoment B raw29509step0 raw29509step0Labels := by
      have hz : ∀ j, raw29509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29509step0 = (fun i j => raw29509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29509step0 raw29509; decide +kernel
      have hl : raw29509step0Labels = raw29509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29509 raw29509Labels permutation346 hz
    _ = mixedMoment B node4973 node4973Labels := by rfl

def raw29510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29510 raw29510Labels = mixedMoment B node5114 node5114Labels := by
  calc
    _ = mixedMoment B node5114 node5114Labels := by rfl

def raw29511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw29511step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29511step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29511step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29511step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29511 raw29511Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw29511 raw29511Labels = mixedMoment B raw29511step0 raw29511step0Labels := by
      have hz : ∀ j, raw29511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29511step0 = (fun i j => raw29511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29511step0 raw29511; decide +kernel
      have hl : raw29511step0Labels = raw29511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29511 raw29511Labels permutation434 hz
    mixedMoment B raw29511step0 raw29511step0Labels = mixedMoment B raw29511step1 raw29511step1Labels := by
      have hz : ∀ j, raw29511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29511step1 = (fun i j => raw29511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29511step1 raw29511step0; decide +kernel
      have hl : raw29511step1Labels = raw29511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29511step0 raw29511step0Labels permutation80 hz
    mixedMoment B raw29511step1 raw29511step1Labels = mixedMoment B raw29511step2 raw29511step2Labels := by
      have ha : raw29511step2 = (fun i j => raw29511step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29511step2 raw29511step1; decide +kernel
      have hl : raw29511step2Labels = raw29511step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29511step1 raw29511step1Labels permutation25 permutation3
    mixedMoment B raw29511step2 raw29511step2Labels = mixedMoment B raw29511step3 raw29511step3Labels := by
      have ha : raw29511step3 = -raw29511step2 := by apply Matrix.ext; change ∀ i j, raw29511step3 i j = -(raw29511step2 i j); unfold raw29511step3 raw29511step2; decide +kernel
      have hl : raw29511step3Labels = raw29511step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29511step3 raw29511step3Labels = mixedMoment B raw29511step4 raw29511step4Labels := by
      have ha : raw29511step4 = raw29511step3 := by apply Matrix.ext; unfold raw29511step4 raw29511step3; decide +kernel
      have hl : raw29511step3Labels = labelEmbedding6 ∘ raw29511step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29511step3 raw29511step3Labels raw29511step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4693 node4693Labels := by rfl

def raw29512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29512step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29512step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29512step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29512step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29512 raw29512Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw29512 raw29512Labels = mixedMoment B raw29512step0 raw29512step0Labels := by
      have hz : ∀ j, raw29512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29512step0 = (fun i j => raw29512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29512step0 raw29512; decide +kernel
      have hl : raw29512step0Labels = raw29512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29512 raw29512Labels permutation434 hz
    mixedMoment B raw29512step0 raw29512step0Labels = mixedMoment B raw29512step1 raw29512step1Labels := by
      have ha : raw29512step1 = (fun i j => raw29512step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29512step1 raw29512step0; decide +kernel
      have hl : raw29512step1Labels = raw29512step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29512step0 raw29512step0Labels permutation125 permutation3
    mixedMoment B raw29512step1 raw29512step1Labels = mixedMoment B raw29512step2 raw29512step2Labels := by
      have ha : raw29512step2 = -raw29512step1 := by apply Matrix.ext; change ∀ i j, raw29512step2 i j = -(raw29512step1 i j); unfold raw29512step2 raw29512step1; decide +kernel
      have hl : raw29512step2Labels = raw29512step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29512step2 raw29512step2Labels = mixedMoment B raw29512step3 raw29512step3Labels := by
      have ha : raw29512step3 = raw29512step2 := by apply Matrix.ext; unfold raw29512step3 raw29512step2; decide +kernel
      have hl : raw29512step2Labels = labelEmbedding6 ∘ raw29512step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29512step2 raw29512step2Labels raw29512step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4686 node4686Labels := by rfl

def raw29513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29513step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29513step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29513step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29513step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29513 raw29513Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw29513 raw29513Labels = mixedMoment B raw29513step0 raw29513step0Labels := by
      have hz : ∀ j, raw29513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29513step0 = (fun i j => raw29513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29513step0 raw29513; decide +kernel
      have hl : raw29513step0Labels = raw29513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29513 raw29513Labels permutation346 hz
    mixedMoment B raw29513step0 raw29513step0Labels = mixedMoment B raw29513step1 raw29513step1Labels := by
      have ha : raw29513step1 = (fun i j => raw29513step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29513step1 raw29513step0; decide +kernel
      have hl : raw29513step1Labels = raw29513step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29513step0 raw29513step0Labels permutation125 permutation3
    mixedMoment B raw29513step1 raw29513step1Labels = mixedMoment B raw29513step2 raw29513step2Labels := by
      have ha : raw29513step2 = -raw29513step1 := by apply Matrix.ext; change ∀ i j, raw29513step2 i j = -(raw29513step1 i j); unfold raw29513step2 raw29513step1; decide +kernel
      have hl : raw29513step2Labels = raw29513step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29513step2 raw29513step2Labels = mixedMoment B raw29513step3 raw29513step3Labels := by
      have ha : raw29513step3 = raw29513step2 := by apply Matrix.ext; unfold raw29513step3 raw29513step2; decide +kernel
      have hl : raw29513step2Labels = labelEmbedding6 ∘ raw29513step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29513step2 raw29513step2Labels raw29513step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4686 node4686Labels := by rfl

def raw29514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29514step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29514step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29514step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29514step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29514 raw29514Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw29514 raw29514Labels = mixedMoment B raw29514step0 raw29514step0Labels := by
      have hz : ∀ j, raw29514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29514step0 = (fun i j => raw29514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29514step0 raw29514; decide +kernel
      have hl : raw29514step0Labels = raw29514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29514 raw29514Labels permutation434 hz
    mixedMoment B raw29514step0 raw29514step0Labels = mixedMoment B raw29514step1 raw29514step1Labels := by
      have hz : ∀ j, raw29514step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29514step1 = (fun i j => raw29514step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29514step1 raw29514step0; decide +kernel
      have hl : raw29514step1Labels = raw29514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29514step0 raw29514step0Labels permutation80 hz
    mixedMoment B raw29514step1 raw29514step1Labels = mixedMoment B raw29514step2 raw29514step2Labels := by
      have ha : raw29514step2 = (fun i j => raw29514step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29514step2 raw29514step1; decide +kernel
      have hl : raw29514step2Labels = raw29514step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29514step1 raw29514step1Labels permutation25 permutation3
    mixedMoment B raw29514step2 raw29514step2Labels = mixedMoment B raw29514step3 raw29514step3Labels := by
      have ha : raw29514step3 = -raw29514step2 := by apply Matrix.ext; change ∀ i j, raw29514step3 i j = -(raw29514step2 i j); unfold raw29514step3 raw29514step2; decide +kernel
      have hl : raw29514step3Labels = raw29514step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29514step3 raw29514step3Labels = mixedMoment B raw29514step4 raw29514step4Labels := by
      have ha : raw29514step4 = raw29514step3 := by apply Matrix.ext; unfold raw29514step4 raw29514step3; decide +kernel
      have hl : raw29514step3Labels = labelEmbedding6 ∘ raw29514step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29514step3 raw29514step3Labels raw29514step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw29515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29515 raw29515Labels = mixedMoment B node3740 node3740Labels := by
  calc
    mixedMoment B raw29515 raw29515Labels = mixedMoment B raw29515step0 raw29515step0Labels := by
      have hz : ∀ j, raw29515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29515step0 = (fun i j => raw29515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29515step0 raw29515; decide +kernel
      have hl : raw29515step0Labels = raw29515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29515 raw29515Labels permutation434 hz
    mixedMoment B raw29515step0 raw29515step0Labels = mixedMoment B raw29515step1 raw29515step1Labels := by
      have hz : ∀ j, raw29515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29515step1 = (fun i j => raw29515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29515step1 raw29515step0; decide +kernel
      have hl : raw29515step1Labels = raw29515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29515step0 raw29515step0Labels permutation80 hz
    mixedMoment B raw29515step1 raw29515step1Labels = mixedMoment B raw29515step2 raw29515step2Labels := by
      have ha : raw29515step2 = (fun i j => raw29515step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29515step2 raw29515step1; decide +kernel
      have hl : raw29515step2Labels = raw29515step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29515step1 raw29515step1Labels permutation15 permutation3
    _ = mixedMoment B node3740 node3740Labels := by rfl

def raw29516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29516 raw29516Labels = mixedMoment B node3739 node3739Labels := by
  calc
    mixedMoment B raw29516 raw29516Labels = mixedMoment B raw29516step0 raw29516step0Labels := by
      have hz : ∀ j, raw29516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29516step0 = (fun i j => raw29516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29516step0 raw29516; decide +kernel
      have hl : raw29516step0Labels = raw29516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29516 raw29516Labels permutation434 hz
    mixedMoment B raw29516step0 raw29516step0Labels = mixedMoment B raw29516step1 raw29516step1Labels := by
      have ha : raw29516step1 = (fun i j => raw29516step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29516step1 raw29516step0; decide +kernel
      have hl : raw29516step1Labels = raw29516step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29516step0 raw29516step0Labels permutation125 permutation3
    mixedMoment B raw29516step1 raw29516step1Labels = mixedMoment B raw29516step2 raw29516step2Labels := by
      have ha : raw29516step2 = -raw29516step1 := by apply Matrix.ext; change ∀ i j, raw29516step2 i j = -(raw29516step1 i j); unfold raw29516step2 raw29516step1; decide +kernel
      have hl : raw29516step2Labels = raw29516step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3739 node3739Labels := by rfl

def raw29517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29517step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29517 raw29517Labels = mixedMoment B node3739 node3739Labels := by
  calc
    mixedMoment B raw29517 raw29517Labels = mixedMoment B raw29517step0 raw29517step0Labels := by
      have hz : ∀ j, raw29517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29517step0 = (fun i j => raw29517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29517step0 raw29517; decide +kernel
      have hl : raw29517step0Labels = raw29517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29517 raw29517Labels permutation346 hz
    mixedMoment B raw29517step0 raw29517step0Labels = mixedMoment B raw29517step1 raw29517step1Labels := by
      have ha : raw29517step1 = (fun i j => raw29517step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29517step1 raw29517step0; decide +kernel
      have hl : raw29517step1Labels = raw29517step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29517step0 raw29517step0Labels permutation125 permutation3
    mixedMoment B raw29517step1 raw29517step1Labels = mixedMoment B raw29517step2 raw29517step2Labels := by
      have ha : raw29517step2 = -raw29517step1 := by apply Matrix.ext; change ∀ i j, raw29517step2 i j = -(raw29517step1 i j); unfold raw29517step2 raw29517step1; decide +kernel
      have hl : raw29517step2Labels = raw29517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3739 node3739Labels := by rfl

def raw29518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29518step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29518step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29518 raw29518Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw29518 raw29518Labels = mixedMoment B raw29518step0 raw29518step0Labels := by
      have hz : ∀ j, raw29518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29518step0 = (fun i j => raw29518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29518step0 raw29518; decide +kernel
      have hl : raw29518step0Labels = raw29518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29518 raw29518Labels permutation434 hz
    mixedMoment B raw29518step0 raw29518step0Labels = mixedMoment B raw29518step1 raw29518step1Labels := by
      have hz : ∀ j, raw29518step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29518step1 = (fun i j => raw29518step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29518step1 raw29518step0; decide +kernel
      have hl : raw29518step1Labels = raw29518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29518step0 raw29518step0Labels permutation80 hz
    mixedMoment B raw29518step1 raw29518step1Labels = mixedMoment B raw29518step2 raw29518step2Labels := by
      have ha : raw29518step2 = (fun i j => raw29518step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29518step2 raw29518step1; decide +kernel
      have hl : raw29518step2Labels = raw29518step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29518step1 raw29518step1Labels permutation25 permutation3
    mixedMoment B raw29518step2 raw29518step2Labels = mixedMoment B raw29518step3 raw29518step3Labels := by
      have ha : raw29518step3 = -raw29518step2 := by apply Matrix.ext; change ∀ i j, raw29518step3 i j = -(raw29518step2 i j); unfold raw29518step3 raw29518step2; decide +kernel
      have hl : raw29518step3Labels = raw29518step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw29519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29519 raw29519Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw29519 raw29519Labels = mixedMoment B raw29519step0 raw29519step0Labels := by
      have hz : ∀ j, raw29519 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29519step0 = (fun i j => raw29519 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29519step0 raw29519; decide +kernel
      have hl : raw29519step0Labels = raw29519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29519 raw29519Labels permutation434 hz
    mixedMoment B raw29519step0 raw29519step0Labels = mixedMoment B raw29519step1 raw29519step1Labels := by
      have ha : raw29519step1 = (fun i j => raw29519step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29519step1 raw29519step0; decide +kernel
      have hl : raw29519step1Labels = raw29519step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29519step0 raw29519step0Labels permutation33 permutation3
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw29520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29520 raw29520Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw29520 raw29520Labels = mixedMoment B raw29520step0 raw29520step0Labels := by
      have ha : raw29520step0 = (fun i j => raw29520 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29520step0 raw29520; decide +kernel
      have hl : raw29520step0Labels = raw29520Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29520 raw29520Labels permutation159 permutation3
    _ = mixedMoment B node2896 node2896Labels := by rfl

def raw29521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29521Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw29521step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29521 raw29521Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw29521 raw29521Labels = mixedMoment B raw29521step0 raw29521step0Labels := by
      have hz : ∀ j, raw29521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29521step0 = (fun i j => raw29521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29521step0 raw29521; decide +kernel
      have hl : raw29521step0Labels = raw29521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29521 raw29521Labels permutation434 hz
    mixedMoment B raw29521step0 raw29521step0Labels = mixedMoment B raw29521step1 raw29521step1Labels := by
      have ha : raw29521step1 = (fun i j => raw29521step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29521step1 raw29521step0; decide +kernel
      have hl : raw29521step1Labels = raw29521step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29521step0 raw29521step0Labels permutation36 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw29522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29522Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29522step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29522 raw29522Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw29522 raw29522Labels = mixedMoment B raw29522step0 raw29522step0Labels := by
      have hz : ∀ j, raw29522 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29522step0 = (fun i j => raw29522 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29522step0 raw29522; decide +kernel
      have hl : raw29522step0Labels = raw29522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29522 raw29522Labels permutation346 hz
    mixedMoment B raw29522step0 raw29522step0Labels = mixedMoment B raw29522step1 raw29522step1Labels := by
      have ha : raw29522step1 = (fun i j => raw29522step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29522step1 raw29522step0; decide +kernel
      have hl : raw29522step1Labels = raw29522step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29522step0 raw29522step0Labels permutation33 permutation3
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw29523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29523Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29523 raw29523Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw29523 raw29523Labels = mixedMoment B raw29523step0 raw29523step0Labels := by
      have ha : raw29523step0 = (fun i j => raw29523 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29523step0 raw29523; decide +kernel
      have hl : raw29523step0Labels = raw29523Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29523 raw29523Labels permutation153 permutation3
    _ = mixedMoment B node2896 node2896Labels := by rfl

def raw29524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29524Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29524step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29524step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw29524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29524step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29524 raw29524Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw29524 raw29524Labels = mixedMoment B raw29524step0 raw29524step0Labels := by
      have hz : ∀ j, raw29524 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29524step0 = (fun i j => raw29524 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29524step0 raw29524; decide +kernel
      have hl : raw29524step0Labels = raw29524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29524 raw29524Labels permutation434 hz
    mixedMoment B raw29524step0 raw29524step0Labels = mixedMoment B raw29524step1 raw29524step1Labels := by
      have hz : ∀ j, raw29524step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29524step1 = (fun i j => raw29524step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29524step1 raw29524step0; decide +kernel
      have hl : raw29524step1Labels = raw29524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29524step0 raw29524step0Labels permutation80 hz
    mixedMoment B raw29524step1 raw29524step1Labels = mixedMoment B raw29524step2 raw29524step2Labels := by
      have ha : raw29524step2 = (fun i j => raw29524step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29524step2 raw29524step1; decide +kernel
      have hl : raw29524step2Labels = raw29524step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29524step1 raw29524step1Labels permutation25 permutation3
    mixedMoment B raw29524step2 raw29524step2Labels = mixedMoment B raw29524step3 raw29524step3Labels := by
      have ha : raw29524step3 = -raw29524step2 := by apply Matrix.ext; change ∀ i j, raw29524step3 i j = -(raw29524step2 i j); unfold raw29524step3 raw29524step2; decide +kernel
      have hl : raw29524step3Labels = raw29524step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw29525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29525step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29525 raw29525Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw29525 raw29525Labels = mixedMoment B raw29525step0 raw29525step0Labels := by
      have hz : ∀ j, raw29525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29525step0 = (fun i j => raw29525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29525step0 raw29525; decide +kernel
      have hl : raw29525step0Labels = raw29525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29525 raw29525Labels permutation434 hz
    mixedMoment B raw29525step0 raw29525step0Labels = mixedMoment B raw29525step1 raw29525step1Labels := by
      have ha : raw29525step1 = (fun i j => raw29525step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29525step1 raw29525step0; decide +kernel
      have hl : raw29525step1Labels = raw29525step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29525step0 raw29525step0Labels permutation125 permutation3
    mixedMoment B raw29525step1 raw29525step1Labels = mixedMoment B raw29525step2 raw29525step2Labels := by
      have ha : raw29525step2 = -raw29525step1 := by apply Matrix.ext; change ∀ i j, raw29525step2 i j = -(raw29525step1 i j); unfold raw29525step2 raw29525step1; decide +kernel
      have hl : raw29525step2Labels = raw29525step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw29526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29526step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29526 raw29526Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw29526 raw29526Labels = mixedMoment B raw29526step0 raw29526step0Labels := by
      have hz : ∀ j, raw29526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29526step0 = (fun i j => raw29526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29526step0 raw29526; decide +kernel
      have hl : raw29526step0Labels = raw29526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29526 raw29526Labels permutation346 hz
    mixedMoment B raw29526step0 raw29526step0Labels = mixedMoment B raw29526step1 raw29526step1Labels := by
      have ha : raw29526step1 = (fun i j => raw29526step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29526step1 raw29526step0; decide +kernel
      have hl : raw29526step1Labels = raw29526step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29526step0 raw29526step0Labels permutation125 permutation3
    mixedMoment B raw29526step1 raw29526step1Labels = mixedMoment B raw29526step2 raw29526step2Labels := by
      have ha : raw29526step2 = -raw29526step1 := by apply Matrix.ext; change ∀ i j, raw29526step2 i j = -(raw29526step1 i j); unfold raw29526step2 raw29526step1; decide +kernel
      have hl : raw29526step2Labels = raw29526step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw29527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29527step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -3, 0], ![1, 1, -2]]
def raw29527step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29527 raw29527Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw29527 raw29527Labels = mixedMoment B raw29527step0 raw29527step0Labels := by
      have hz : ∀ j, raw29527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29527step0 = (fun i j => raw29527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29527step0 raw29527; decide +kernel
      have hl : raw29527step0Labels = raw29527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29527 raw29527Labels permutation434 hz
    mixedMoment B raw29527step0 raw29527step0Labels = mixedMoment B raw29527step1 raw29527step1Labels := by
      have hz : ∀ j, raw29527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29527step1 = (fun i j => raw29527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29527step1 raw29527step0; decide +kernel
      have hl : raw29527step1Labels = raw29527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29527step0 raw29527step0Labels permutation80 hz
    mixedMoment B raw29527step1 raw29527step1Labels = mixedMoment B raw29527step2 raw29527step2Labels := by
      have ha : raw29527step2 = (fun i j => raw29527step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29527step2 raw29527step1; decide +kernel
      have hl : raw29527step2Labels = raw29527step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29527step1 raw29527step1Labels permutation25 permutation3
    mixedMoment B raw29527step2 raw29527step2Labels = mixedMoment B raw29527step3 raw29527step3Labels := by
      have ha : raw29527step3 = -raw29527step2 := by apply Matrix.ext; change ∀ i j, raw29527step3 i j = -(raw29527step2 i j); unfold raw29527step3 raw29527step2; decide +kernel
      have hl : raw29527step3Labels = raw29527step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw29528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw29528step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29528step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29528step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29528 raw29528Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw29528 raw29528Labels = mixedMoment B raw29528step0 raw29528step0Labels := by
      have hz : ∀ j, raw29528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29528step0 = (fun i j => raw29528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29528step0 raw29528; decide +kernel
      have hl : raw29528step0Labels = raw29528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29528 raw29528Labels permutation434 hz
    mixedMoment B raw29528step0 raw29528step0Labels = mixedMoment B raw29528step1 raw29528step1Labels := by
      have hz : ∀ j, raw29528step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29528step1 = (fun i j => raw29528step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29528step1 raw29528step0; decide +kernel
      have hl : raw29528step1Labels = raw29528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29528step0 raw29528step0Labels permutation80 hz
    mixedMoment B raw29528step1 raw29528step1Labels = mixedMoment B raw29528step2 raw29528step2Labels := by
      have ha : raw29528step2 = (fun i j => raw29528step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29528step2 raw29528step1; decide +kernel
      have hl : raw29528step2Labels = raw29528step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29528step1 raw29528step1Labels permutation24 permutation2
    mixedMoment B raw29528step2 raw29528step2Labels = mixedMoment B raw29528step3 raw29528step3Labels := by
      have ha : raw29528step3 = -raw29528step2 := by apply Matrix.ext; change ∀ i j, raw29528step3 i j = -(raw29528step2 i j); unfold raw29528step3 raw29528step2; decide +kernel
      have hl : raw29528step3Labels = raw29528step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5390 node5390Labels := by rfl

def raw29529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29529 raw29529Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw29529 raw29529Labels = mixedMoment B raw29529step0 raw29529step0Labels := by
      have hz : ∀ j, raw29529 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29529step0 = (fun i j => raw29529 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29529step0 raw29529; decide +kernel
      have hl : raw29529step0Labels = raw29529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29529 raw29529Labels permutation434 hz
    mixedMoment B raw29529step0 raw29529step0Labels = mixedMoment B raw29529step1 raw29529step1Labels := by
      have ha : raw29529step1 = (fun i j => raw29529step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29529step1 raw29529step0; decide +kernel
      have hl : raw29529step1Labels = raw29529step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29529step0 raw29529step0Labels permutation127 permutation2
    mixedMoment B raw29529step1 raw29529step1Labels = mixedMoment B raw29529step2 raw29529step2Labels := by
      have ha : raw29529step2 = -raw29529step1 := by apply Matrix.ext; change ∀ i j, raw29529step2 i j = -(raw29529step1 i j); unfold raw29529step2 raw29529step1; decide +kernel
      have hl : raw29529step2Labels = raw29529step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw29530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29530 raw29530Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw29530 raw29530Labels = mixedMoment B raw29530step0 raw29530step0Labels := by
      have hz : ∀ j, raw29530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29530step0 = (fun i j => raw29530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29530step0 raw29530; decide +kernel
      have hl : raw29530step0Labels = raw29530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29530 raw29530Labels permutation346 hz
    mixedMoment B raw29530step0 raw29530step0Labels = mixedMoment B raw29530step1 raw29530step1Labels := by
      have ha : raw29530step1 = (fun i j => raw29530step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29530step1 raw29530step0; decide +kernel
      have hl : raw29530step1Labels = raw29530step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29530step0 raw29530step0Labels permutation127 permutation2
    mixedMoment B raw29530step1 raw29530step1Labels = mixedMoment B raw29530step2 raw29530step2Labels := by
      have ha : raw29530step2 = -raw29530step1 := by apply Matrix.ext; change ∀ i j, raw29530step2 i j = -(raw29530step1 i j); unfold raw29530step2 raw29530step1; decide +kernel
      have hl : raw29530step2Labels = raw29530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw29531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0]]
def raw29531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29531step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29531step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29531step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29531 raw29531Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw29531 raw29531Labels = mixedMoment B raw29531step0 raw29531step0Labels := by
      have hz : ∀ j, raw29531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29531step0 = (fun i j => raw29531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29531step0 raw29531; decide +kernel
      have hl : raw29531step0Labels = raw29531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29531 raw29531Labels permutation434 hz
    mixedMoment B raw29531step0 raw29531step0Labels = mixedMoment B raw29531step1 raw29531step1Labels := by
      have hz : ∀ j, raw29531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29531step1 = (fun i j => raw29531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29531step1 raw29531step0; decide +kernel
      have hl : raw29531step1Labels = raw29531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29531step0 raw29531step0Labels permutation80 hz
    mixedMoment B raw29531step1 raw29531step1Labels = mixedMoment B raw29531step2 raw29531step2Labels := by
      have ha : raw29531step2 = (fun i j => raw29531step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29531step2 raw29531step1; decide +kernel
      have hl : raw29531step2Labels = raw29531step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29531step1 raw29531step1Labels permutation25 permutation2
    mixedMoment B raw29531step2 raw29531step2Labels = mixedMoment B raw29531step3 raw29531step3Labels := by
      have ha : raw29531step3 = -raw29531step2 := by apply Matrix.ext; change ∀ i j, raw29531step3 i j = -(raw29531step2 i j); unfold raw29531step3 raw29531step2; decide +kernel
      have hl : raw29531step3Labels = raw29531step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw29532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29532step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29532step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29532 raw29532Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw29532 raw29532Labels = mixedMoment B raw29532step0 raw29532step0Labels := by
      have hz : ∀ j, raw29532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29532step0 = (fun i j => raw29532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29532step0 raw29532; decide +kernel
      have hl : raw29532step0Labels = raw29532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29532 raw29532Labels permutation434 hz
    mixedMoment B raw29532step0 raw29532step0Labels = mixedMoment B raw29532step1 raw29532step1Labels := by
      have ha : raw29532step1 = (fun i j => raw29532step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29532step1 raw29532step0; decide +kernel
      have hl : raw29532step1Labels = raw29532step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29532step0 raw29532step0Labels permutation32 permutation3
    mixedMoment B raw29532step1 raw29532step1Labels = mixedMoment B raw29532step2 raw29532step2Labels := by
      have ha : raw29532step2 = raw29532step1 := by apply Matrix.ext; unfold raw29532step2 raw29532step1; decide +kernel
      have hl : raw29532step1Labels = labelEmbedding6 ∘ raw29532step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29532step1 raw29532step1Labels raw29532step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw29533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29533step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29533step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29533 raw29533Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw29533 raw29533Labels = mixedMoment B raw29533step0 raw29533step0Labels := by
      have hz : ∀ j, raw29533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29533step0 = (fun i j => raw29533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29533step0 raw29533; decide +kernel
      have hl : raw29533step0Labels = raw29533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29533 raw29533Labels permutation434 hz
    mixedMoment B raw29533step0 raw29533step0Labels = mixedMoment B raw29533step1 raw29533step1Labels := by
      have ha : raw29533step1 = (fun i j => raw29533step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29533step1 raw29533step0; decide +kernel
      have hl : raw29533step1Labels = raw29533step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29533step0 raw29533step0Labels permutation32 permutation3
    mixedMoment B raw29533step1 raw29533step1Labels = mixedMoment B raw29533step2 raw29533step2Labels := by
      have ha : raw29533step2 = raw29533step1 := by apply Matrix.ext; unfold raw29533step2 raw29533step1; decide +kernel
      have hl : raw29533step1Labels = labelEmbedding6 ∘ raw29533step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29533step1 raw29533step1Labels raw29533step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw29534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29534step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29534 raw29534Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw29534 raw29534Labels = mixedMoment B raw29534step0 raw29534step0Labels := by
      have ha : raw29534step0 = (fun i j => raw29534 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29534step0 raw29534; decide +kernel
      have hl : raw29534step0Labels = raw29534Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29534 raw29534Labels permutation200 permutation3
    mixedMoment B raw29534step0 raw29534step0Labels = mixedMoment B raw29534step1 raw29534step1Labels := by
      have ha : raw29534step1 = raw29534step0 := by apply Matrix.ext; unfold raw29534step1 raw29534step0; decide +kernel
      have hl : raw29534step0Labels = labelEmbedding6 ∘ raw29534step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29534step0 raw29534step0Labels raw29534step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw29535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29535step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29535 raw29535Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw29535 raw29535Labels = mixedMoment B raw29535step0 raw29535step0Labels := by
      have hz : ∀ j, raw29535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29535step0 = (fun i j => raw29535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29535step0 raw29535; decide +kernel
      have hl : raw29535step0Labels = raw29535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29535 raw29535Labels permutation434 hz
    mixedMoment B raw29535step0 raw29535step0Labels = mixedMoment B raw29535step1 raw29535step1Labels := by
      have ha : raw29535step1 = (fun i j => raw29535step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29535step1 raw29535step0; decide +kernel
      have hl : raw29535step1Labels = raw29535step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29535step0 raw29535step0Labels permutation33 permutation3
    mixedMoment B raw29535step1 raw29535step1Labels = mixedMoment B raw29535step2 raw29535step2Labels := by
      have ha : raw29535step2 = raw29535step1 := by apply Matrix.ext; unfold raw29535step2 raw29535step1; decide +kernel
      have hl : raw29535step1Labels = labelEmbedding6 ∘ raw29535step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29535step1 raw29535step1Labels raw29535step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw29536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29536step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29536step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29536 raw29536Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw29536 raw29536Labels = mixedMoment B raw29536step0 raw29536step0Labels := by
      have hz : ∀ j, raw29536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29536step0 = (fun i j => raw29536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29536step0 raw29536; decide +kernel
      have hl : raw29536step0Labels = raw29536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29536 raw29536Labels permutation346 hz
    mixedMoment B raw29536step0 raw29536step0Labels = mixedMoment B raw29536step1 raw29536step1Labels := by
      have ha : raw29536step1 = (fun i j => raw29536step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29536step1 raw29536step0; decide +kernel
      have hl : raw29536step1Labels = raw29536step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29536step0 raw29536step0Labels permutation32 permutation3
    mixedMoment B raw29536step1 raw29536step1Labels = mixedMoment B raw29536step2 raw29536step2Labels := by
      have ha : raw29536step2 = raw29536step1 := by apply Matrix.ext; unfold raw29536step2 raw29536step1; decide +kernel
      have hl : raw29536step1Labels = labelEmbedding6 ∘ raw29536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29536step1 raw29536step1Labels raw29536step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw29537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29537step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29537step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29537step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29537 raw29537Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw29537 raw29537Labels = mixedMoment B raw29537step0 raw29537step0Labels := by
      have hz : ∀ j, raw29537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29537step0 = (fun i j => raw29537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29537step0 raw29537; decide +kernel
      have hl : raw29537step0Labels = raw29537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29537 raw29537Labels permutation346 hz
    mixedMoment B raw29537step0 raw29537step0Labels = mixedMoment B raw29537step1 raw29537step1Labels := by
      have ha : raw29537step1 = (fun i j => raw29537step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29537step1 raw29537step0; decide +kernel
      have hl : raw29537step1Labels = raw29537step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29537step0 raw29537step0Labels permutation32 permutation3
    mixedMoment B raw29537step1 raw29537step1Labels = mixedMoment B raw29537step2 raw29537step2Labels := by
      have ha : raw29537step2 = raw29537step1 := by apply Matrix.ext; unfold raw29537step2 raw29537step1; decide +kernel
      have hl : raw29537step1Labels = labelEmbedding6 ∘ raw29537step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29537step1 raw29537step1Labels raw29537step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw29538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29538step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29538 raw29538Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw29538 raw29538Labels = mixedMoment B raw29538step0 raw29538step0Labels := by
      have ha : raw29538step0 = (fun i j => raw29538 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29538step0 raw29538; decide +kernel
      have hl : raw29538step0Labels = raw29538Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29538 raw29538Labels permutation176 permutation3
    mixedMoment B raw29538step0 raw29538step0Labels = mixedMoment B raw29538step1 raw29538step1Labels := by
      have ha : raw29538step1 = raw29538step0 := by apply Matrix.ext; unfold raw29538step1 raw29538step0; decide +kernel
      have hl : raw29538step0Labels = labelEmbedding6 ∘ raw29538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29538step0 raw29538step0Labels raw29538step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw29539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29539step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29539 raw29539Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw29539 raw29539Labels = mixedMoment B raw29539step0 raw29539step0Labels := by
      have hz : ∀ j, raw29539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29539step0 = (fun i j => raw29539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29539step0 raw29539; decide +kernel
      have hl : raw29539step0Labels = raw29539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29539 raw29539Labels permutation346 hz
    mixedMoment B raw29539step0 raw29539step0Labels = mixedMoment B raw29539step1 raw29539step1Labels := by
      have ha : raw29539step1 = (fun i j => raw29539step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29539step1 raw29539step0; decide +kernel
      have hl : raw29539step1Labels = raw29539step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29539step0 raw29539step0Labels permutation33 permutation3
    mixedMoment B raw29539step1 raw29539step1Labels = mixedMoment B raw29539step2 raw29539step2Labels := by
      have ha : raw29539step2 = raw29539step1 := by apply Matrix.ext; unfold raw29539step2 raw29539step1; decide +kernel
      have hl : raw29539step1Labels = labelEmbedding6 ∘ raw29539step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29539step1 raw29539step1Labels raw29539step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw29540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29540step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29540step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29540step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29540 raw29540Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw29540 raw29540Labels = mixedMoment B raw29540step0 raw29540step0Labels := by
      have hz : ∀ j, raw29540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29540step0 = (fun i j => raw29540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29540step0 raw29540; decide +kernel
      have hl : raw29540step0Labels = raw29540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29540 raw29540Labels permutation434 hz
    mixedMoment B raw29540step0 raw29540step0Labels = mixedMoment B raw29540step1 raw29540step1Labels := by
      have hz : ∀ j, raw29540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29540step1 = (fun i j => raw29540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29540step1 raw29540step0; decide +kernel
      have hl : raw29540step1Labels = raw29540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29540step0 raw29540step0Labels permutation80 hz
    mixedMoment B raw29540step1 raw29540step1Labels = mixedMoment B raw29540step2 raw29540step2Labels := by
      have ha : raw29540step2 = (fun i j => raw29540step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29540step2 raw29540step1; decide +kernel
      have hl : raw29540step2Labels = raw29540step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29540step1 raw29540step1Labels permutation9 permutation3
    mixedMoment B raw29540step2 raw29540step2Labels = mixedMoment B raw29540step3 raw29540step3Labels := by
      have ha : raw29540step3 = raw29540step2 := by apply Matrix.ext; unfold raw29540step3 raw29540step2; decide +kernel
      have hl : raw29540step2Labels = labelEmbedding6 ∘ raw29540step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29540step2 raw29540step2Labels raw29540step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4361 node4361Labels := by rfl

def raw29541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29541step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29541step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29541step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29541 raw29541Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw29541 raw29541Labels = mixedMoment B raw29541step0 raw29541step0Labels := by
      have hz : ∀ j, raw29541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29541step0 = (fun i j => raw29541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29541step0 raw29541; decide +kernel
      have hl : raw29541step0Labels = raw29541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29541 raw29541Labels permutation434 hz
    mixedMoment B raw29541step0 raw29541step0Labels = mixedMoment B raw29541step1 raw29541step1Labels := by
      have hz : ∀ j, raw29541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29541step1 = (fun i j => raw29541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29541step1 raw29541step0; decide +kernel
      have hl : raw29541step1Labels = raw29541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29541step0 raw29541step0Labels permutation80 hz
    mixedMoment B raw29541step1 raw29541step1Labels = mixedMoment B raw29541step2 raw29541step2Labels := by
      have ha : raw29541step2 = (fun i j => raw29541step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29541step2 raw29541step1; decide +kernel
      have hl : raw29541step2Labels = raw29541step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29541step1 raw29541step1Labels permutation9 permutation3
    mixedMoment B raw29541step2 raw29541step2Labels = mixedMoment B raw29541step3 raw29541step3Labels := by
      have ha : raw29541step3 = raw29541step2 := by apply Matrix.ext; unfold raw29541step3 raw29541step2; decide +kernel
      have hl : raw29541step2Labels = labelEmbedding6 ∘ raw29541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29541step2 raw29541step2Labels raw29541step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4953 node4953Labels := by rfl

def raw29542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29542step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29542 raw29542Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw29542 raw29542Labels = mixedMoment B raw29542step0 raw29542step0Labels := by
      have hz : ∀ j, raw29542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29542step0 = (fun i j => raw29542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29542step0 raw29542; decide +kernel
      have hl : raw29542step0Labels = raw29542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29542 raw29542Labels permutation434 hz
    mixedMoment B raw29542step0 raw29542step0Labels = mixedMoment B raw29542step1 raw29542step1Labels := by
      have ha : raw29542step1 = (fun i j => raw29542step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29542step1 raw29542step0; decide +kernel
      have hl : raw29542step1Labels = raw29542step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29542step0 raw29542step0Labels permutation127 permutation2
    mixedMoment B raw29542step1 raw29542step1Labels = mixedMoment B raw29542step2 raw29542step2Labels := by
      have ha : raw29542step2 = -raw29542step1 := by apply Matrix.ext; change ∀ i j, raw29542step2 i j = -(raw29542step1 i j); unfold raw29542step2 raw29542step1; decide +kernel
      have hl : raw29542step2Labels = raw29542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw29543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29543 raw29543Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw29543 raw29543Labels = mixedMoment B raw29543step0 raw29543step0Labels := by
      have hz : ∀ j, raw29543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29543step0 = (fun i j => raw29543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29543step0 raw29543; decide +kernel
      have hl : raw29543step0Labels = raw29543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29543 raw29543Labels permutation346 hz
    mixedMoment B raw29543step0 raw29543step0Labels = mixedMoment B raw29543step1 raw29543step1Labels := by
      have ha : raw29543step1 = (fun i j => raw29543step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29543step1 raw29543step0; decide +kernel
      have hl : raw29543step1Labels = raw29543step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29543step0 raw29543step0Labels permutation127 permutation2
    mixedMoment B raw29543step1 raw29543step1Labels = mixedMoment B raw29543step2 raw29543step2Labels := by
      have ha : raw29543step2 = -raw29543step1 := by apply Matrix.ext; change ∀ i j, raw29543step2 i j = -(raw29543step1 i j); unfold raw29543step2 raw29543step1; decide +kernel
      have hl : raw29543step2Labels = raw29543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw29544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -1, -2], ![1, -1, 0]]
def raw29544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29544step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29544step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29544step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29544 raw29544Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw29544 raw29544Labels = mixedMoment B raw29544step0 raw29544step0Labels := by
      have hz : ∀ j, raw29544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29544step0 = (fun i j => raw29544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29544step0 raw29544; decide +kernel
      have hl : raw29544step0Labels = raw29544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29544 raw29544Labels permutation434 hz
    mixedMoment B raw29544step0 raw29544step0Labels = mixedMoment B raw29544step1 raw29544step1Labels := by
      have hz : ∀ j, raw29544step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29544step1 = (fun i j => raw29544step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29544step1 raw29544step0; decide +kernel
      have hl : raw29544step1Labels = raw29544step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29544step0 raw29544step0Labels permutation80 hz
    mixedMoment B raw29544step1 raw29544step1Labels = mixedMoment B raw29544step2 raw29544step2Labels := by
      have ha : raw29544step2 = (fun i j => raw29544step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29544step2 raw29544step1; decide +kernel
      have hl : raw29544step2Labels = raw29544step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29544step1 raw29544step1Labels permutation25 permutation2
    mixedMoment B raw29544step2 raw29544step2Labels = mixedMoment B raw29544step3 raw29544step3Labels := by
      have ha : raw29544step3 = -raw29544step2 := by apply Matrix.ext; change ∀ i j, raw29544step3 i j = -(raw29544step2 i j); unfold raw29544step3 raw29544step2; decide +kernel
      have hl : raw29544step3Labels = raw29544step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw29545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw29545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw29545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29545 raw29545Labels = mixedMoment B node3741 node3741Labels := by
  calc
    mixedMoment B raw29545 raw29545Labels = mixedMoment B raw29545step0 raw29545step0Labels := by
      have hz : ∀ j, raw29545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29545step0 = (fun i j => raw29545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29545step0 raw29545; decide +kernel
      have hl : raw29545step0Labels = raw29545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29545 raw29545Labels permutation434 hz
    mixedMoment B raw29545step0 raw29545step0Labels = mixedMoment B raw29545step1 raw29545step1Labels := by
      have hz : ∀ j, raw29545step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29545step1 = (fun i j => raw29545step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29545step1 raw29545step0; decide +kernel
      have hl : raw29545step1Labels = raw29545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29545step0 raw29545step0Labels permutation80 hz
    mixedMoment B raw29545step1 raw29545step1Labels = mixedMoment B raw29545step2 raw29545step2Labels := by
      have ha : raw29545step2 = (fun i j => raw29545step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29545step2 raw29545step1; decide +kernel
      have hl : raw29545step2Labels = raw29545step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29545step1 raw29545step1Labels permutation30 permutation3
    mixedMoment B raw29545step2 raw29545step2Labels = mixedMoment B raw29545step3 raw29545step3Labels := by
      have ha : raw29545step3 = -raw29545step2 := by apply Matrix.ext; change ∀ i j, raw29545step3 i j = -(raw29545step2 i j); unfold raw29545step3 raw29545step2; decide +kernel
      have hl : raw29545step3Labels = raw29545step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3741 node3741Labels := by rfl

def raw29546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29546 raw29546Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw29546 raw29546Labels = mixedMoment B raw29546step0 raw29546step0Labels := by
      have hz : ∀ j, raw29546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29546step0 = (fun i j => raw29546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29546step0 raw29546; decide +kernel
      have hl : raw29546step0Labels = raw29546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29546 raw29546Labels permutation434 hz
    mixedMoment B raw29546step0 raw29546step0Labels = mixedMoment B raw29546step1 raw29546step1Labels := by
      have ha : raw29546step1 = (fun i j => raw29546step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29546step1 raw29546step0; decide +kernel
      have hl : raw29546step1Labels = raw29546step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29546step0 raw29546step0Labels permutation149 permutation3
    mixedMoment B raw29546step1 raw29546step1Labels = mixedMoment B raw29546step2 raw29546step2Labels := by
      have ha : raw29546step2 = -raw29546step1 := by apply Matrix.ext; change ∀ i j, raw29546step2 i j = -(raw29546step1 i j); unfold raw29546step2 raw29546step1; decide +kernel
      have hl : raw29546step2Labels = raw29546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw29547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29547 raw29547Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw29547 raw29547Labels = mixedMoment B raw29547step0 raw29547step0Labels := by
      have hz : ∀ j, raw29547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29547step0 = (fun i j => raw29547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29547step0 raw29547; decide +kernel
      have hl : raw29547step0Labels = raw29547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29547 raw29547Labels permutation346 hz
    mixedMoment B raw29547step0 raw29547step0Labels = mixedMoment B raw29547step1 raw29547step1Labels := by
      have ha : raw29547step1 = (fun i j => raw29547step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29547step1 raw29547step0; decide +kernel
      have hl : raw29547step1Labels = raw29547step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29547step0 raw29547step0Labels permutation149 permutation3
    mixedMoment B raw29547step1 raw29547step1Labels = mixedMoment B raw29547step2 raw29547step2Labels := by
      have ha : raw29547step2 = -raw29547step1 := by apply Matrix.ext; change ∀ i j, raw29547step2 i j = -(raw29547step1 i j); unfold raw29547step2 raw29547step1; decide +kernel
      have hl : raw29547step2Labels = raw29547step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw29548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0]]
def raw29548step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29548 raw29548Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw29548 raw29548Labels = mixedMoment B raw29548step0 raw29548step0Labels := by
      have hz : ∀ j, raw29548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29548step0 = (fun i j => raw29548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29548step0 raw29548; decide +kernel
      have hl : raw29548step0Labels = raw29548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29548 raw29548Labels permutation434 hz
    mixedMoment B raw29548step0 raw29548step0Labels = mixedMoment B raw29548step1 raw29548step1Labels := by
      have hz : ∀ j, raw29548step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29548step1 = (fun i j => raw29548step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29548step1 raw29548step0; decide +kernel
      have hl : raw29548step1Labels = raw29548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29548step0 raw29548step0Labels permutation80 hz
    mixedMoment B raw29548step1 raw29548step1Labels = mixedMoment B raw29548step2 raw29548step2Labels := by
      have ha : raw29548step2 = (fun i j => raw29548step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29548step2 raw29548step1; decide +kernel
      have hl : raw29548step2Labels = raw29548step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29548step1 raw29548step1Labels permutation9 permutation3
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw29549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29549 raw29549Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw29549 raw29549Labels = mixedMoment B raw29549step0 raw29549step0Labels := by
      have hz : ∀ j, raw29549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29549step0 = (fun i j => raw29549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29549step0 raw29549; decide +kernel
      have hl : raw29549step0Labels = raw29549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29549 raw29549Labels permutation434 hz
    mixedMoment B raw29549step0 raw29549step0Labels = mixedMoment B raw29549step1 raw29549step1Labels := by
      have ha : raw29549step1 = (fun i j => raw29549step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29549step1 raw29549step0; decide +kernel
      have hl : raw29549step1Labels = raw29549step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29549step0 raw29549step0Labels permutation32 permutation3
    _ = mixedMoment B node932 node932Labels := by rfl

def raw29550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29550 raw29550Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw29550 raw29550Labels = mixedMoment B raw29550step0 raw29550step0Labels := by
      have hz : ∀ j, raw29550 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29550step0 = (fun i j => raw29550 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29550step0 raw29550; decide +kernel
      have hl : raw29550step0Labels = raw29550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29550 raw29550Labels permutation434 hz
    mixedMoment B raw29550step0 raw29550step0Labels = mixedMoment B raw29550step1 raw29550step1Labels := by
      have ha : raw29550step1 = (fun i j => raw29550step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29550step1 raw29550step0; decide +kernel
      have hl : raw29550step1Labels = raw29550step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29550step0 raw29550step0Labels permutation32 permutation3
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw29551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29551 raw29551Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw29551 raw29551Labels = mixedMoment B raw29551step0 raw29551step0Labels := by
      have ha : raw29551step0 = (fun i j => raw29551 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29551step0 raw29551; decide +kernel
      have hl : raw29551step0Labels = raw29551Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29551 raw29551Labels permutation200 permutation3
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw29552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29552 raw29552Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw29552 raw29552Labels = mixedMoment B raw29552step0 raw29552step0Labels := by
      have hz : ∀ j, raw29552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29552step0 = (fun i j => raw29552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29552step0 raw29552; decide +kernel
      have hl : raw29552step0Labels = raw29552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29552 raw29552Labels permutation434 hz
    mixedMoment B raw29552step0 raw29552step0Labels = mixedMoment B raw29552step1 raw29552step1Labels := by
      have ha : raw29552step1 = (fun i j => raw29552step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29552step1 raw29552step0; decide +kernel
      have hl : raw29552step1Labels = raw29552step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29552step0 raw29552step0Labels permutation33 permutation3
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw29553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29553 raw29553Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw29553 raw29553Labels = mixedMoment B raw29553step0 raw29553step0Labels := by
      have hz : ∀ j, raw29553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29553step0 = (fun i j => raw29553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29553step0 raw29553; decide +kernel
      have hl : raw29553step0Labels = raw29553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29553 raw29553Labels permutation346 hz
    mixedMoment B raw29553step0 raw29553step0Labels = mixedMoment B raw29553step1 raw29553step1Labels := by
      have ha : raw29553step1 = (fun i j => raw29553step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29553step1 raw29553step0; decide +kernel
      have hl : raw29553step1Labels = raw29553step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29553step0 raw29553step0Labels permutation32 permutation3
    _ = mixedMoment B node932 node932Labels := by rfl

def raw29554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29554 raw29554Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw29554 raw29554Labels = mixedMoment B raw29554step0 raw29554step0Labels := by
      have hz : ∀ j, raw29554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29554step0 = (fun i j => raw29554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29554step0 raw29554; decide +kernel
      have hl : raw29554step0Labels = raw29554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29554 raw29554Labels permutation346 hz
    mixedMoment B raw29554step0 raw29554step0Labels = mixedMoment B raw29554step1 raw29554step1Labels := by
      have ha : raw29554step1 = (fun i j => raw29554step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29554step1 raw29554step0; decide +kernel
      have hl : raw29554step1Labels = raw29554step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29554step0 raw29554step0Labels permutation32 permutation3
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw29555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29555 raw29555Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw29555 raw29555Labels = mixedMoment B raw29555step0 raw29555step0Labels := by
      have ha : raw29555step0 = (fun i j => raw29555 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29555step0 raw29555; decide +kernel
      have hl : raw29555step0Labels = raw29555Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29555 raw29555Labels permutation176 permutation3
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw29556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29556 raw29556Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw29556 raw29556Labels = mixedMoment B raw29556step0 raw29556step0Labels := by
      have hz : ∀ j, raw29556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29556step0 = (fun i j => raw29556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29556step0 raw29556; decide +kernel
      have hl : raw29556step0Labels = raw29556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29556 raw29556Labels permutation346 hz
    mixedMoment B raw29556step0 raw29556step0Labels = mixedMoment B raw29556step1 raw29556step1Labels := by
      have ha : raw29556step1 = (fun i j => raw29556step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29556step1 raw29556step0; decide +kernel
      have hl : raw29556step1Labels = raw29556step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29556step0 raw29556step0Labels permutation33 permutation3
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw29557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29557step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29557step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29557 raw29557Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw29557 raw29557Labels = mixedMoment B raw29557step0 raw29557step0Labels := by
      have hz : ∀ j, raw29557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29557step0 = (fun i j => raw29557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29557step0 raw29557; decide +kernel
      have hl : raw29557step0Labels = raw29557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29557 raw29557Labels permutation434 hz
    mixedMoment B raw29557step0 raw29557step0Labels = mixedMoment B raw29557step1 raw29557step1Labels := by
      have hz : ∀ j, raw29557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29557step1 = (fun i j => raw29557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29557step1 raw29557step0; decide +kernel
      have hl : raw29557step1Labels = raw29557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29557step0 raw29557step0Labels permutation80 hz
    mixedMoment B raw29557step1 raw29557step1Labels = mixedMoment B raw29557step2 raw29557step2Labels := by
      have ha : raw29557step2 = (fun i j => raw29557step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29557step2 raw29557step1; decide +kernel
      have hl : raw29557step2Labels = raw29557step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29557step1 raw29557step1Labels permutation9 permutation3
    _ = mixedMoment B node939 node939Labels := by rfl

def raw29558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -1, -2], ![2, -2, 0]]
def raw29558step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29558 raw29558Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw29558 raw29558Labels = mixedMoment B raw29558step0 raw29558step0Labels := by
      have hz : ∀ j, raw29558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29558step0 = (fun i j => raw29558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29558step0 raw29558; decide +kernel
      have hl : raw29558step0Labels = raw29558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29558 raw29558Labels permutation434 hz
    mixedMoment B raw29558step0 raw29558step0Labels = mixedMoment B raw29558step1 raw29558step1Labels := by
      have hz : ∀ j, raw29558step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29558step1 = (fun i j => raw29558step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29558step1 raw29558step0; decide +kernel
      have hl : raw29558step1Labels = raw29558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29558step0 raw29558step0Labels permutation80 hz
    mixedMoment B raw29558step1 raw29558step1Labels = mixedMoment B raw29558step2 raw29558step2Labels := by
      have ha : raw29558step2 = (fun i j => raw29558step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29558step2 raw29558step1; decide +kernel
      have hl : raw29558step2Labels = raw29558step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29558step1 raw29558step1Labels permutation9 permutation3
    _ = mixedMoment B node2345 node2345Labels := by rfl

def raw29559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29559 raw29559Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw29559 raw29559Labels = mixedMoment B raw29559step0 raw29559step0Labels := by
      have hz : ∀ j, raw29559 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29559step0 = (fun i j => raw29559 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29559step0 raw29559; decide +kernel
      have hl : raw29559step0Labels = raw29559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29559 raw29559Labels permutation434 hz
    mixedMoment B raw29559step0 raw29559step0Labels = mixedMoment B raw29559step1 raw29559step1Labels := by
      have ha : raw29559step1 = (fun i j => raw29559step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29559step1 raw29559step0; decide +kernel
      have hl : raw29559step1Labels = raw29559step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29559step0 raw29559step0Labels permutation39 permutation3
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw29560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29560 raw29560Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw29560 raw29560Labels = mixedMoment B raw29560step0 raw29560step0Labels := by
      have hz : ∀ j, raw29560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29560step0 = (fun i j => raw29560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29560step0 raw29560; decide +kernel
      have hl : raw29560step0Labels = raw29560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29560 raw29560Labels permutation346 hz
    mixedMoment B raw29560step0 raw29560step0Labels = mixedMoment B raw29560step1 raw29560step1Labels := by
      have ha : raw29560step1 = (fun i j => raw29560step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29560step1 raw29560step0; decide +kernel
      have hl : raw29560step1Labels = raw29560step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29560step0 raw29560step0Labels permutation39 permutation3
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw29561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw29561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -1, -2], ![1, -1, 0]]
def raw29561step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29561 raw29561Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw29561 raw29561Labels = mixedMoment B raw29561step0 raw29561step0Labels := by
      have hz : ∀ j, raw29561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29561step0 = (fun i j => raw29561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29561step0 raw29561; decide +kernel
      have hl : raw29561step0Labels = raw29561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29561 raw29561Labels permutation434 hz
    mixedMoment B raw29561step0 raw29561step0Labels = mixedMoment B raw29561step1 raw29561step1Labels := by
      have hz : ∀ j, raw29561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29561step1 = (fun i j => raw29561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29561step1 raw29561step0; decide +kernel
      have hl : raw29561step1Labels = raw29561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29561step0 raw29561step0Labels permutation80 hz
    mixedMoment B raw29561step1 raw29561step1Labels = mixedMoment B raw29561step2 raw29561step2Labels := by
      have ha : raw29561step2 = (fun i j => raw29561step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29561step2 raw29561step1; decide +kernel
      have hl : raw29561step2Labels = raw29561step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29561step1 raw29561step1Labels permutation9 permutation3
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw29562 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29562step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29562 raw29562Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw29562 raw29562Labels = mixedMoment B raw29562step0 raw29562step0Labels := by
      have hz : ∀ j, raw29562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29562step0 = (fun i j => raw29562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29562step0 raw29562; decide +kernel
      have hl : raw29562step0Labels = raw29562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29562 raw29562Labels permutation434 hz
    mixedMoment B raw29562step0 raw29562step0Labels = mixedMoment B raw29562step1 raw29562step1Labels := by
      have hz : ∀ j, raw29562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29562step1 = (fun i j => raw29562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29562step1 raw29562step0; decide +kernel
      have hl : raw29562step1Labels = raw29562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29562step0 raw29562step0Labels permutation80 hz
    mixedMoment B raw29562step1 raw29562step1Labels = mixedMoment B raw29562step2 raw29562step2Labels := by
      have ha : raw29562step2 = (fun i j => raw29562step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29562step2 raw29562step1; decide +kernel
      have hl : raw29562step2Labels = raw29562step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29562step1 raw29562step1Labels permutation9 permutation7
    mixedMoment B raw29562step2 raw29562step2Labels = mixedMoment B raw29562step3 raw29562step3Labels := by
      have ha : raw29562step3 = raw29562step2 := by apply Matrix.ext; unfold raw29562step3 raw29562step2; decide +kernel
      have hl : raw29562step2Labels = labelEmbedding10 ∘ raw29562step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29562step2 raw29562step2Labels raw29562step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw29563 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29563step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29563 raw29563Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw29563 raw29563Labels = mixedMoment B raw29563step0 raw29563step0Labels := by
      have hz : ∀ j, raw29563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29563step0 = (fun i j => raw29563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29563step0 raw29563; decide +kernel
      have hl : raw29563step0Labels = raw29563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29563 raw29563Labels permutation434 hz
    mixedMoment B raw29563step0 raw29563step0Labels = mixedMoment B raw29563step1 raw29563step1Labels := by
      have ha : raw29563step1 = (fun i j => raw29563step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29563step1 raw29563step0; decide +kernel
      have hl : raw29563step1Labels = raw29563step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29563step0 raw29563step0Labels permutation33 permutation7
    mixedMoment B raw29563step1 raw29563step1Labels = mixedMoment B raw29563step2 raw29563step2Labels := by
      have ha : raw29563step2 = raw29563step1 := by apply Matrix.ext; unfold raw29563step2 raw29563step1; decide +kernel
      have hl : raw29563step1Labels = labelEmbedding10 ∘ raw29563step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29563step1 raw29563step1Labels raw29563step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw29564 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29564step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29564 raw29564Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw29564 raw29564Labels = mixedMoment B raw29564step0 raw29564step0Labels := by
      have hz : ∀ j, raw29564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29564step0 = (fun i j => raw29564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29564step0 raw29564; decide +kernel
      have hl : raw29564step0Labels = raw29564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29564 raw29564Labels permutation346 hz
    mixedMoment B raw29564step0 raw29564step0Labels = mixedMoment B raw29564step1 raw29564step1Labels := by
      have ha : raw29564step1 = (fun i j => raw29564step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29564step1 raw29564step0; decide +kernel
      have hl : raw29564step1Labels = raw29564step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29564step0 raw29564step0Labels permutation33 permutation7
    mixedMoment B raw29564step1 raw29564step1Labels = mixedMoment B raw29564step2 raw29564step2Labels := by
      have ha : raw29564step2 = raw29564step1 := by apply Matrix.ext; unfold raw29564step2 raw29564step1; decide +kernel
      have hl : raw29564step1Labels = labelEmbedding10 ∘ raw29564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29564step1 raw29564step1Labels raw29564step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw29565 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29565step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29565step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29565 raw29565Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw29565 raw29565Labels = mixedMoment B raw29565step0 raw29565step0Labels := by
      have hz : ∀ j, raw29565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29565step0 = (fun i j => raw29565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29565step0 raw29565; decide +kernel
      have hl : raw29565step0Labels = raw29565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29565 raw29565Labels permutation434 hz
    mixedMoment B raw29565step0 raw29565step0Labels = mixedMoment B raw29565step1 raw29565step1Labels := by
      have hz : ∀ j, raw29565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29565step1 = (fun i j => raw29565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29565step1 raw29565step0; decide +kernel
      have hl : raw29565step1Labels = raw29565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29565step0 raw29565step0Labels permutation80 hz
    mixedMoment B raw29565step1 raw29565step1Labels = mixedMoment B raw29565step2 raw29565step2Labels := by
      have ha : raw29565step2 = (fun i j => raw29565step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29565step2 raw29565step1; decide +kernel
      have hl : raw29565step2Labels = raw29565step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29565step1 raw29565step1Labels permutation9 permutation7
    mixedMoment B raw29565step2 raw29565step2Labels = mixedMoment B raw29565step3 raw29565step3Labels := by
      have ha : raw29565step3 = raw29565step2 := by apply Matrix.ext; unfold raw29565step3 raw29565step2; decide +kernel
      have hl : raw29565step2Labels = labelEmbedding10 ∘ raw29565step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29565step2 raw29565step2Labels raw29565step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw29566 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29566step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29566 raw29566Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw29566 raw29566Labels = mixedMoment B raw29566step0 raw29566step0Labels := by
      have hz : ∀ j, raw29566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29566step0 = (fun i j => raw29566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29566step0 raw29566; decide +kernel
      have hl : raw29566step0Labels = raw29566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29566 raw29566Labels permutation434 hz
    mixedMoment B raw29566step0 raw29566step0Labels = mixedMoment B raw29566step1 raw29566step1Labels := by
      have hz : ∀ j, raw29566step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29566step1 = (fun i j => raw29566step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29566step1 raw29566step0; decide +kernel
      have hl : raw29566step1Labels = raw29566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29566step0 raw29566step0Labels permutation80 hz
    mixedMoment B raw29566step1 raw29566step1Labels = mixedMoment B raw29566step2 raw29566step2Labels := by
      have ha : raw29566step2 = (fun i j => raw29566step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29566step2 raw29566step1; decide +kernel
      have hl : raw29566step2Labels = raw29566step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29566step1 raw29566step1Labels permutation9 permutation7
    mixedMoment B raw29566step2 raw29566step2Labels = mixedMoment B raw29566step3 raw29566step3Labels := by
      have ha : raw29566step3 = raw29566step2 := by apply Matrix.ext; unfold raw29566step3 raw29566step2; decide +kernel
      have hl : raw29566step2Labels = labelEmbedding10 ∘ raw29566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29566step2 raw29566step2Labels raw29566step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5111 node5111Labels := by rfl

def raw29567 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29567step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29567step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29567 raw29567Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw29567 raw29567Labels = mixedMoment B raw29567step0 raw29567step0Labels := by
      have hz : ∀ j, raw29567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29567step0 = (fun i j => raw29567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29567step0 raw29567; decide +kernel
      have hl : raw29567step0Labels = raw29567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29567 raw29567Labels permutation434 hz
    mixedMoment B raw29567step0 raw29567step0Labels = mixedMoment B raw29567step1 raw29567step1Labels := by
      have hz : ∀ j, raw29567step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29567step1 = (fun i j => raw29567step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29567step1 raw29567step0; decide +kernel
      have hl : raw29567step1Labels = raw29567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29567step0 raw29567step0Labels permutation80 hz
    mixedMoment B raw29567step1 raw29567step1Labels = mixedMoment B raw29567step2 raw29567step2Labels := by
      have ha : raw29567step2 = (fun i j => raw29567step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29567step2 raw29567step1; decide +kernel
      have hl : raw29567step2Labels = raw29567step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29567step1 raw29567step1Labels permutation8 permutation6
    mixedMoment B raw29567step2 raw29567step2Labels = mixedMoment B raw29567step3 raw29567step3Labels := by
      have ha : raw29567step3 = raw29567step2 := by apply Matrix.ext; unfold raw29567step3 raw29567step2; decide +kernel
      have hl : raw29567step2Labels = labelEmbedding9 ∘ raw29567step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29567step2 raw29567step2Labels raw29567step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
