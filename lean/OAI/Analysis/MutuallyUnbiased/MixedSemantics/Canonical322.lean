import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41216Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw41216step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0]]
def raw41216step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41216step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41216step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41216 raw41216Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw41216 raw41216Labels = mixedMoment B raw41216step0 raw41216step0Labels := by
      have hz : ∀ j, raw41216 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41216step0 = (fun i j => raw41216 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41216step0 raw41216; decide +kernel
      have hl : raw41216step0Labels = raw41216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41216 raw41216Labels permutation520 hz
    mixedMoment B raw41216step0 raw41216step0Labels = mixedMoment B raw41216step1 raw41216step1Labels := by
      have hz : ∀ j, raw41216step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41216step1 = (fun i j => raw41216step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41216step1 raw41216step0; decide +kernel
      have hl : raw41216step1Labels = raw41216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41216step0 raw41216step0Labels permutation104 hz
    mixedMoment B raw41216step1 raw41216step1Labels = mixedMoment B raw41216step2 raw41216step2Labels := by
      have ha : raw41216step2 = (fun i j => raw41216step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41216step2 raw41216step1; decide +kernel
      have hl : raw41216step2Labels = raw41216step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41216step1 raw41216step1Labels permutation31 permutation3
    mixedMoment B raw41216step2 raw41216step2Labels = mixedMoment B raw41216step3 raw41216step3Labels := by
      have ha : raw41216step3 = -raw41216step2 := by apply Matrix.ext; change ∀ i j, raw41216step3 i j = -(raw41216step2 i j); unfold raw41216step3 raw41216step2; decide +kernel
      have hl : raw41216step3Labels = raw41216step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw41217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw41217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1]]
def raw41217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41217 raw41217Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw41217 raw41217Labels = mixedMoment B raw41217step0 raw41217step0Labels := by
      have hz : ∀ j, raw41217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41217step0 = (fun i j => raw41217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41217step0 raw41217; decide +kernel
      have hl : raw41217step0Labels = raw41217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41217 raw41217Labels permutation434 hz
    mixedMoment B raw41217step0 raw41217step0Labels = mixedMoment B raw41217step1 raw41217step1Labels := by
      have ha : raw41217step1 = (fun i j => raw41217step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41217step1 raw41217step0; decide +kernel
      have hl : raw41217step1Labels = raw41217step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41217step0 raw41217step0Labels permutation151 permutation3
    mixedMoment B raw41217step1 raw41217step1Labels = mixedMoment B raw41217step2 raw41217step2Labels := by
      have ha : raw41217step2 = -raw41217step1 := by apply Matrix.ext; change ∀ i j, raw41217step2 i j = -(raw41217step1 i j); unfold raw41217step2 raw41217step1; decide +kernel
      have hl : raw41217step2Labels = raw41217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw41218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw41218Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![3, -1, -2]]
def raw41218step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41218step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41218 raw41218Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw41218 raw41218Labels = mixedMoment B raw41218step0 raw41218step0Labels := by
      have hz : ∀ j, raw41218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41218step0 = (fun i j => raw41218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41218step0 raw41218; decide +kernel
      have hl : raw41218step0Labels = raw41218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41218 raw41218Labels permutation434 hz
    mixedMoment B raw41218step0 raw41218step0Labels = mixedMoment B raw41218step1 raw41218step1Labels := by
      have ha : raw41218step1 = (fun i j => raw41218step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41218step1 raw41218step0; decide +kernel
      have hl : raw41218step1Labels = raw41218step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41218step0 raw41218step0Labels permutation151 permutation3
    mixedMoment B raw41218step1 raw41218step1Labels = mixedMoment B raw41218step2 raw41218step2Labels := by
      have ha : raw41218step2 = -raw41218step1 := by apply Matrix.ext; change ∀ i j, raw41218step2 i j = -(raw41218step1 i j); unfold raw41218step2 raw41218step1; decide +kernel
      have hl : raw41218step2Labels = raw41218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw41219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41219Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw41219step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41219 raw41219Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw41219 raw41219Labels = mixedMoment B raw41219step0 raw41219step0Labels := by
      have hz : ∀ j, raw41219 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41219step0 = (fun i j => raw41219 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41219step0 raw41219; decide +kernel
      have hl : raw41219step0Labels = raw41219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41219 raw41219Labels permutation434 hz
    mixedMoment B raw41219step0 raw41219step0Labels = mixedMoment B raw41219step1 raw41219step1Labels := by
      have ha : raw41219step1 = (fun i j => raw41219step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41219step1 raw41219step0; decide +kernel
      have hl : raw41219step1Labels = raw41219step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41219step0 raw41219step0Labels permutation151 permutation3
    mixedMoment B raw41219step1 raw41219step1Labels = mixedMoment B raw41219step2 raw41219step2Labels := by
      have ha : raw41219step2 = -raw41219step1 := by apply Matrix.ext; change ∀ i j, raw41219step2 i j = -(raw41219step1 i j); unfold raw41219step2 raw41219step1; decide +kernel
      have hl : raw41219step2Labels = raw41219step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw41220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41220Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw41220step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41220 raw41220Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw41220 raw41220Labels = mixedMoment B raw41220step0 raw41220step0Labels := by
      have hz : ∀ j, raw41220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41220step0 = (fun i j => raw41220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41220step0 raw41220; decide +kernel
      have hl : raw41220step0Labels = raw41220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41220 raw41220Labels permutation434 hz
    mixedMoment B raw41220step0 raw41220step0Labels = mixedMoment B raw41220step1 raw41220step1Labels := by
      have ha : raw41220step1 = (fun i j => raw41220step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41220step1 raw41220step0; decide +kernel
      have hl : raw41220step1Labels = raw41220step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41220step0 raw41220step0Labels permutation151 permutation3
    mixedMoment B raw41220step1 raw41220step1Labels = mixedMoment B raw41220step2 raw41220step2Labels := by
      have ha : raw41220step2 = -raw41220step1 := by apply Matrix.ext; change ∀ i j, raw41220step2 i j = -(raw41220step1 i j); unfold raw41220step2 raw41220step1; decide +kernel
      have hl : raw41220step2Labels = raw41220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw41221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41221Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 0, -2]]
def raw41221step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41221step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41221 raw41221Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw41221 raw41221Labels = mixedMoment B raw41221step0 raw41221step0Labels := by
      have hz : ∀ j, raw41221 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41221step0 = (fun i j => raw41221 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41221step0 raw41221; decide +kernel
      have hl : raw41221step0Labels = raw41221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41221 raw41221Labels permutation434 hz
    mixedMoment B raw41221step0 raw41221step0Labels = mixedMoment B raw41221step1 raw41221step1Labels := by
      have ha : raw41221step1 = (fun i j => raw41221step0 (permutation118 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41221step1 raw41221step0; decide +kernel
      have hl : raw41221step1Labels = raw41221step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41221step0 raw41221step0Labels permutation118 permutation6
    mixedMoment B raw41221step1 raw41221step1Labels = mixedMoment B raw41221step2 raw41221step2Labels := by
      have ha : raw41221step2 = -raw41221step1 := by apply Matrix.ext; change ∀ i j, raw41221step2 i j = -(raw41221step1 i j); unfold raw41221step2 raw41221step1; decide +kernel
      have hl : raw41221step2Labels = raw41221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw41222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw41222Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41222 raw41222Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw41222 raw41222Labels = mixedMoment B raw41222step0 raw41222step0Labels := by
      have ha : raw41222step0 = (fun i j => raw41222 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41222step0 raw41222; decide +kernel
      have hl : raw41222step0Labels = raw41222Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41222 raw41222Labels permutation664 permutation3
    mixedMoment B raw41222step0 raw41222step0Labels = mixedMoment B raw41222step1 raw41222step1Labels := by
      have ha : raw41222step1 = -raw41222step0 := by apply Matrix.ext; change ∀ i j, raw41222step1 i j = -(raw41222step0 i j); unfold raw41222step1 raw41222step0; decide +kernel
      have hl : raw41222step1Labels = raw41222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw41223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41223Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41223step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41223step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41223 raw41223Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw41223 raw41223Labels = mixedMoment B raw41223step0 raw41223step0Labels := by
      have ha : raw41223step0 = (fun i j => raw41223 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41223step0 raw41223; decide +kernel
      have hl : raw41223step0Labels = raw41223Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41223 raw41223Labels permutation688 permutation3
    mixedMoment B raw41223step0 raw41223step0Labels = mixedMoment B raw41223step1 raw41223step1Labels := by
      have ha : raw41223step1 = -raw41223step0 := by apply Matrix.ext; change ∀ i j, raw41223step1 i j = -(raw41223step0 i j); unfold raw41223step1 raw41223step0; decide +kernel
      have hl : raw41223step1Labels = raw41223step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw41224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41224Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41224 raw41224Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw41224 raw41224Labels = mixedMoment B raw41224step0 raw41224step0Labels := by
      have ha : raw41224step0 = (fun i j => raw41224 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41224step0 raw41224; decide +kernel
      have hl : raw41224step0Labels = raw41224Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41224 raw41224Labels permutation688 permutation3
    mixedMoment B raw41224step0 raw41224step0Labels = mixedMoment B raw41224step1 raw41224step1Labels := by
      have ha : raw41224step1 = -raw41224step0 := by apply Matrix.ext; change ∀ i j, raw41224step1 i j = -(raw41224step0 i j); unfold raw41224step1 raw41224step0; decide +kernel
      have hl : raw41224step1Labels = raw41224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw41225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41225Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41225 raw41225Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw41225 raw41225Labels = mixedMoment B raw41225step0 raw41225step0Labels := by
      have ha : raw41225step0 = (fun i j => raw41225 (permutation477 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41225step0 raw41225; decide +kernel
      have hl : raw41225step0Labels = raw41225Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41225 raw41225Labels permutation477 permutation6
    mixedMoment B raw41225step0 raw41225step0Labels = mixedMoment B raw41225step1 raw41225step1Labels := by
      have ha : raw41225step1 = -raw41225step0 := by apply Matrix.ext; change ∀ i j, raw41225step1 i j = -(raw41225step0 i j); unfold raw41225step1 raw41225step0; decide +kernel
      have hl : raw41225step1Labels = raw41225step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw41226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw41226Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1]]
def raw41226step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![3, -2, -1]]
def raw41226step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41226step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41226step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41226 raw41226Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw41226 raw41226Labels = mixedMoment B raw41226step0 raw41226step0Labels := by
      have hz : ∀ j, raw41226 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41226step0 = (fun i j => raw41226 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41226step0 raw41226; decide +kernel
      have hl : raw41226step0Labels = raw41226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41226 raw41226Labels permutation520 hz
    mixedMoment B raw41226step0 raw41226step0Labels = mixedMoment B raw41226step1 raw41226step1Labels := by
      have hz : ∀ j, raw41226step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41226step1 = (fun i j => raw41226step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41226step1 raw41226step0; decide +kernel
      have hl : raw41226step1Labels = raw41226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41226step0 raw41226step0Labels permutation104 hz
    mixedMoment B raw41226step1 raw41226step1Labels = mixedMoment B raw41226step2 raw41226step2Labels := by
      have ha : raw41226step2 = (fun i j => raw41226step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41226step2 raw41226step1; decide +kernel
      have hl : raw41226step2Labels = raw41226step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41226step1 raw41226step1Labels permutation31 permutation3
    mixedMoment B raw41226step2 raw41226step2Labels = mixedMoment B raw41226step3 raw41226step3Labels := by
      have ha : raw41226step3 = -raw41226step2 := by apply Matrix.ext; change ∀ i j, raw41226step3 i j = -(raw41226step2 i j); unfold raw41226step3 raw41226step2; decide +kernel
      have hl : raw41226step3Labels = raw41226step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw41227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw41227Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![3, -1, -2]]
def raw41227step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41227step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41227 raw41227Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw41227 raw41227Labels = mixedMoment B raw41227step0 raw41227step0Labels := by
      have hz : ∀ j, raw41227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41227step0 = (fun i j => raw41227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41227step0 raw41227; decide +kernel
      have hl : raw41227step0Labels = raw41227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41227 raw41227Labels permutation434 hz
    mixedMoment B raw41227step0 raw41227step0Labels = mixedMoment B raw41227step1 raw41227step1Labels := by
      have ha : raw41227step1 = (fun i j => raw41227step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41227step1 raw41227step0; decide +kernel
      have hl : raw41227step1Labels = raw41227step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41227step0 raw41227step0Labels permutation151 permutation3
    mixedMoment B raw41227step1 raw41227step1Labels = mixedMoment B raw41227step2 raw41227step2Labels := by
      have ha : raw41227step2 = -raw41227step1 := by apply Matrix.ext; change ∀ i j, raw41227step2 i j = -(raw41227step1 i j); unfold raw41227step2 raw41227step1; decide +kernel
      have hl : raw41227step2Labels = raw41227step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw41228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41228Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw41228step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41228 raw41228Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw41228 raw41228Labels = mixedMoment B raw41228step0 raw41228step0Labels := by
      have hz : ∀ j, raw41228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41228step0 = (fun i j => raw41228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41228step0 raw41228; decide +kernel
      have hl : raw41228step0Labels = raw41228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41228 raw41228Labels permutation434 hz
    mixedMoment B raw41228step0 raw41228step0Labels = mixedMoment B raw41228step1 raw41228step1Labels := by
      have ha : raw41228step1 = (fun i j => raw41228step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41228step1 raw41228step0; decide +kernel
      have hl : raw41228step1Labels = raw41228step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41228step0 raw41228step0Labels permutation151 permutation3
    mixedMoment B raw41228step1 raw41228step1Labels = mixedMoment B raw41228step2 raw41228step2Labels := by
      have ha : raw41228step2 = -raw41228step1 := by apply Matrix.ext; change ∀ i j, raw41228step2 i j = -(raw41228step1 i j); unfold raw41228step2 raw41228step1; decide +kernel
      have hl : raw41228step2Labels = raw41228step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw41229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41229Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw41229step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41229step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41229 raw41229Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw41229 raw41229Labels = mixedMoment B raw41229step0 raw41229step0Labels := by
      have hz : ∀ j, raw41229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41229step0 = (fun i j => raw41229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41229step0 raw41229; decide +kernel
      have hl : raw41229step0Labels = raw41229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41229 raw41229Labels permutation434 hz
    mixedMoment B raw41229step0 raw41229step0Labels = mixedMoment B raw41229step1 raw41229step1Labels := by
      have ha : raw41229step1 = (fun i j => raw41229step0 (permutation94 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41229step1 raw41229step0; decide +kernel
      have hl : raw41229step1Labels = raw41229step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41229step0 raw41229step0Labels permutation94 permutation6
    mixedMoment B raw41229step1 raw41229step1Labels = mixedMoment B raw41229step2 raw41229step2Labels := by
      have ha : raw41229step2 = -raw41229step1 := by apply Matrix.ext; change ∀ i j, raw41229step2 i j = -(raw41229step1 i j); unfold raw41229step2 raw41229step1; decide +kernel
      have hl : raw41229step2Labels = raw41229step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw41230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41230Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41230 raw41230Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw41230 raw41230Labels = mixedMoment B raw41230step0 raw41230step0Labels := by
      have ha : raw41230step0 = (fun i j => raw41230 (permutation391 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41230step0 raw41230; decide +kernel
      have hl : raw41230step0Labels = raw41230Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41230 raw41230Labels permutation391 permutation6
    mixedMoment B raw41230step0 raw41230step0Labels = mixedMoment B raw41230step1 raw41230step1Labels := by
      have ha : raw41230step1 = -raw41230step0 := by apply Matrix.ext; change ∀ i j, raw41230step1 i j = -(raw41230step0 i j); unfold raw41230step1 raw41230step0; decide +kernel
      have hl : raw41230step1Labels = raw41230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw41231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41231Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![3, -1, -2]]
def raw41231step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![3, -1, -2]]
def raw41231step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw41231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41231step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41231step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41231 raw41231Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw41231 raw41231Labels = mixedMoment B raw41231step0 raw41231step0Labels := by
      have hz : ∀ j, raw41231 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41231step0 = (fun i j => raw41231 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41231step0 raw41231; decide +kernel
      have hl : raw41231step0Labels = raw41231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41231 raw41231Labels permutation520 hz
    mixedMoment B raw41231step0 raw41231step0Labels = mixedMoment B raw41231step1 raw41231step1Labels := by
      have hz : ∀ j, raw41231step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41231step1 = (fun i j => raw41231step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41231step1 raw41231step0; decide +kernel
      have hl : raw41231step1Labels = raw41231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41231step0 raw41231step0Labels permutation104 hz
    mixedMoment B raw41231step1 raw41231step1Labels = mixedMoment B raw41231step2 raw41231step2Labels := by
      have ha : raw41231step2 = (fun i j => raw41231step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41231step2 raw41231step1; decide +kernel
      have hl : raw41231step2Labels = raw41231step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41231step1 raw41231step1Labels permutation22 permutation6
    mixedMoment B raw41231step2 raw41231step2Labels = mixedMoment B raw41231step3 raw41231step3Labels := by
      have ha : raw41231step3 = -raw41231step2 := by apply Matrix.ext; change ∀ i j, raw41231step3 i j = -(raw41231step2 i j); unfold raw41231step3 raw41231step2; decide +kernel
      have hl : raw41231step3Labels = raw41231step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw41232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw41232step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41232 raw41232Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw41232 raw41232Labels = mixedMoment B raw41232step0 raw41232step0Labels := by
      have hz : ∀ j, raw41232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41232step0 = (fun i j => raw41232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41232step0 raw41232; decide +kernel
      have hl : raw41232step0Labels = raw41232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41232 raw41232Labels permutation434 hz
    mixedMoment B raw41232step0 raw41232step0Labels = mixedMoment B raw41232step1 raw41232step1Labels := by
      have ha : raw41232step1 = (fun i j => raw41232step0 (permutation94 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41232step1 raw41232step0; decide +kernel
      have hl : raw41232step1Labels = raw41232step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41232step0 raw41232step0Labels permutation94 permutation6
    mixedMoment B raw41232step1 raw41232step1Labels = mixedMoment B raw41232step2 raw41232step2Labels := by
      have ha : raw41232step2 = -raw41232step1 := by apply Matrix.ext; change ∀ i j, raw41232step2 i j = -(raw41232step1 i j); unfold raw41232step2 raw41232step1; decide +kernel
      have hl : raw41232step2Labels = raw41232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw41233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw41233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw41233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0]]
def raw41233step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41233step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41233step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41233step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41233 raw41233Labels = mixedMoment B node3908 node3908Labels := by
  calc
    mixedMoment B raw41233 raw41233Labels = mixedMoment B raw41233step0 raw41233step0Labels := by
      have hz : ∀ j, raw41233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41233step0 = (fun i j => raw41233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41233step0 raw41233; decide +kernel
      have hl : raw41233step0Labels = raw41233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41233 raw41233Labels permutation434 hz
    mixedMoment B raw41233step0 raw41233step0Labels = mixedMoment B raw41233step1 raw41233step1Labels := by
      have hz : ∀ j, raw41233step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41233step1 = (fun i j => raw41233step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41233step1 raw41233step0; decide +kernel
      have hl : raw41233step1Labels = raw41233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41233step0 raw41233step0Labels permutation80 hz
    mixedMoment B raw41233step1 raw41233step1Labels = mixedMoment B raw41233step2 raw41233step2Labels := by
      have ha : raw41233step2 = (fun i j => raw41233step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41233step2 raw41233step1; decide +kernel
      have hl : raw41233step2Labels = raw41233step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41233step1 raw41233step1Labels permutation31 permutation3
    mixedMoment B raw41233step2 raw41233step2Labels = mixedMoment B raw41233step3 raw41233step3Labels := by
      have ha : raw41233step3 = -raw41233step2 := by apply Matrix.ext; change ∀ i j, raw41233step3 i j = -(raw41233step2 i j); unfold raw41233step3 raw41233step2; decide +kernel
      have hl : raw41233step3Labels = raw41233step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3908 node3908Labels := by rfl

def raw41234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw41234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw41234step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1]]
def raw41234step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw41234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw41234step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41234 raw41234Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw41234 raw41234Labels = mixedMoment B raw41234step0 raw41234step0Labels := by
      have hz : ∀ j, raw41234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41234step0 = (fun i j => raw41234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41234step0 raw41234; decide +kernel
      have hl : raw41234step0Labels = raw41234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41234 raw41234Labels permutation434 hz
    mixedMoment B raw41234step0 raw41234step0Labels = mixedMoment B raw41234step1 raw41234step1Labels := by
      have hz : ∀ j, raw41234step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41234step1 = (fun i j => raw41234step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41234step1 raw41234step0; decide +kernel
      have hl : raw41234step1Labels = raw41234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41234step0 raw41234step0Labels permutation80 hz
    mixedMoment B raw41234step1 raw41234step1Labels = mixedMoment B raw41234step2 raw41234step2Labels := by
      have ha : raw41234step2 = (fun i j => raw41234step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41234step2 raw41234step1; decide +kernel
      have hl : raw41234step2Labels = raw41234step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41234step1 raw41234step1Labels permutation23 permutation6
    mixedMoment B raw41234step2 raw41234step2Labels = mixedMoment B raw41234step3 raw41234step3Labels := by
      have ha : raw41234step3 = -raw41234step2 := by apply Matrix.ext; change ∀ i j, raw41234step3 i j = -(raw41234step2 i j); unfold raw41234step3 raw41234step2; decide +kernel
      have hl : raw41234step3Labels = raw41234step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw41235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw41235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw41235step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -3, 3], ![2, 0, -2]]
def raw41235step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41235step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41235 raw41235Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw41235 raw41235Labels = mixedMoment B raw41235step0 raw41235step0Labels := by
      have hz : ∀ j, raw41235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41235step0 = (fun i j => raw41235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41235step0 raw41235; decide +kernel
      have hl : raw41235step0Labels = raw41235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41235 raw41235Labels permutation434 hz
    mixedMoment B raw41235step0 raw41235step0Labels = mixedMoment B raw41235step1 raw41235step1Labels := by
      have hz : ∀ j, raw41235step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41235step1 = (fun i j => raw41235step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41235step1 raw41235step0; decide +kernel
      have hl : raw41235step1Labels = raw41235step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41235step0 raw41235step0Labels permutation80 hz
    mixedMoment B raw41235step1 raw41235step1Labels = mixedMoment B raw41235step2 raw41235step2Labels := by
      have ha : raw41235step2 = (fun i j => raw41235step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41235step2 raw41235step1; decide +kernel
      have hl : raw41235step2Labels = raw41235step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41235step1 raw41235step1Labels permutation22 permutation6
    mixedMoment B raw41235step2 raw41235step2Labels = mixedMoment B raw41235step3 raw41235step3Labels := by
      have ha : raw41235step3 = -raw41235step2 := by apply Matrix.ext; change ∀ i j, raw41235step3 i j = -(raw41235step2 i j); unfold raw41235step3 raw41235step2; decide +kernel
      have hl : raw41235step3Labels = raw41235step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw41236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw41236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw41236step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2]]
def raw41236step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41236step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41236step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41236step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41236 raw41236Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw41236 raw41236Labels = mixedMoment B raw41236step0 raw41236step0Labels := by
      have hz : ∀ j, raw41236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41236step0 = (fun i j => raw41236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41236step0 raw41236; decide +kernel
      have hl : raw41236step0Labels = raw41236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41236 raw41236Labels permutation434 hz
    mixedMoment B raw41236step0 raw41236step0Labels = mixedMoment B raw41236step1 raw41236step1Labels := by
      have hz : ∀ j, raw41236step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41236step1 = (fun i j => raw41236step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41236step1 raw41236step0; decide +kernel
      have hl : raw41236step1Labels = raw41236step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41236step0 raw41236step0Labels permutation80 hz
    mixedMoment B raw41236step1 raw41236step1Labels = mixedMoment B raw41236step2 raw41236step2Labels := by
      have ha : raw41236step2 = (fun i j => raw41236step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41236step2 raw41236step1; decide +kernel
      have hl : raw41236step2Labels = raw41236step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41236step1 raw41236step1Labels permutation29 permutation6
    mixedMoment B raw41236step2 raw41236step2Labels = mixedMoment B raw41236step3 raw41236step3Labels := by
      have ha : raw41236step3 = -raw41236step2 := by apply Matrix.ext; change ∀ i j, raw41236step3 i j = -(raw41236step2 i j); unfold raw41236step3 raw41236step2; decide +kernel
      have hl : raw41236step3Labels = raw41236step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

def raw41237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw41237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw41237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1]]
def raw41237step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41237step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41237 raw41237Labels = mixedMoment B node4049 node4049Labels := by
  calc
    mixedMoment B raw41237 raw41237Labels = mixedMoment B raw41237step0 raw41237step0Labels := by
      have hz : ∀ j, raw41237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41237step0 = (fun i j => raw41237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41237step0 raw41237; decide +kernel
      have hl : raw41237step0Labels = raw41237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41237 raw41237Labels permutation434 hz
    mixedMoment B raw41237step0 raw41237step0Labels = mixedMoment B raw41237step1 raw41237step1Labels := by
      have hz : ∀ j, raw41237step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41237step1 = (fun i j => raw41237step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41237step1 raw41237step0; decide +kernel
      have hl : raw41237step1Labels = raw41237step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41237step0 raw41237step0Labels permutation80 hz
    mixedMoment B raw41237step1 raw41237step1Labels = mixedMoment B raw41237step2 raw41237step2Labels := by
      have ha : raw41237step2 = (fun i j => raw41237step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41237step2 raw41237step1; decide +kernel
      have hl : raw41237step2Labels = raw41237step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41237step1 raw41237step1Labels permutation8 permutation3
    _ = mixedMoment B node4049 node4049Labels := by rfl

def raw41238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41238 raw41238Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw41238 raw41238Labels = mixedMoment B raw41238step0 raw41238step0Labels := by
      have hz : ∀ j, raw41238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41238step0 = (fun i j => raw41238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41238step0 raw41238; decide +kernel
      have hl : raw41238step0Labels = raw41238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41238 raw41238Labels permutation346 hz
    mixedMoment B raw41238step0 raw41238step0Labels = mixedMoment B raw41238step1 raw41238step1Labels := by
      have ha : raw41238step1 = (fun i j => raw41238step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41238step1 raw41238step0; decide +kernel
      have hl : raw41238step1Labels = raw41238step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41238step0 raw41238step0Labels permutation145 permutation3
    mixedMoment B raw41238step1 raw41238step1Labels = mixedMoment B raw41238step2 raw41238step2Labels := by
      have ha : raw41238step2 = -raw41238step1 := by apply Matrix.ext; change ∀ i j, raw41238step2 i j = -(raw41238step1 i j); unfold raw41238step2 raw41238step1; decide +kernel
      have hl : raw41238step2Labels = raw41238step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw41239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41239step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41239step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41239 raw41239Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw41239 raw41239Labels = mixedMoment B raw41239step0 raw41239step0Labels := by
      have hz : ∀ j, raw41239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41239step0 = (fun i j => raw41239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41239step0 raw41239; decide +kernel
      have hl : raw41239step0Labels = raw41239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41239 raw41239Labels permutation346 hz
    mixedMoment B raw41239step0 raw41239step0Labels = mixedMoment B raw41239step1 raw41239step1Labels := by
      have ha : raw41239step1 = (fun i j => raw41239step0 (permutation118 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41239step1 raw41239step0; decide +kernel
      have hl : raw41239step1Labels = raw41239step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41239step0 raw41239step0Labels permutation118 permutation6
    mixedMoment B raw41239step1 raw41239step1Labels = mixedMoment B raw41239step2 raw41239step2Labels := by
      have ha : raw41239step2 = -raw41239step1 := by apply Matrix.ext; change ∀ i j, raw41239step2 i j = -(raw41239step1 i j); unfold raw41239step2 raw41239step1; decide +kernel
      have hl : raw41239step2Labels = raw41239step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw41240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41240 raw41240Labels = mixedMoment B node4047 node4047Labels := by
  calc
    mixedMoment B raw41240 raw41240Labels = mixedMoment B raw41240step0 raw41240step0Labels := by
      have hz : ∀ j, raw41240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41240step0 = (fun i j => raw41240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41240step0 raw41240; decide +kernel
      have hl : raw41240step0Labels = raw41240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41240 raw41240Labels permutation346 hz
    mixedMoment B raw41240step0 raw41240step0Labels = mixedMoment B raw41240step1 raw41240step1Labels := by
      have ha : raw41240step1 = (fun i j => raw41240step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41240step1 raw41240step0; decide +kernel
      have hl : raw41240step1Labels = raw41240step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41240step0 raw41240step0Labels permutation32 permutation3
    _ = mixedMoment B node4047 node4047Labels := by rfl

def raw41241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41241 raw41241Labels = mixedMoment B node4048 node4048Labels := by
  calc
    mixedMoment B raw41241 raw41241Labels = mixedMoment B raw41241step0 raw41241step0Labels := by
      have hz : ∀ j, raw41241 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41241step0 = (fun i j => raw41241 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41241step0 raw41241; decide +kernel
      have hl : raw41241step0Labels = raw41241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41241 raw41241Labels permutation346 hz
    mixedMoment B raw41241step0 raw41241step0Labels = mixedMoment B raw41241step1 raw41241step1Labels := by
      have ha : raw41241step1 = (fun i j => raw41241step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41241step1 raw41241step0; decide +kernel
      have hl : raw41241step1Labels = raw41241step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41241step0 raw41241step0Labels permutation32 permutation3
    _ = mixedMoment B node4048 node4048Labels := by rfl

def raw41242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41242 raw41242Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw41242 raw41242Labels = mixedMoment B raw41242step0 raw41242step0Labels := by
      have hz : ∀ j, raw41242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41242step0 = (fun i j => raw41242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41242step0 raw41242; decide +kernel
      have hl : raw41242step0Labels = raw41242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41242 raw41242Labels permutation346 hz
    mixedMoment B raw41242step0 raw41242step0Labels = mixedMoment B raw41242step1 raw41242step1Labels := by
      have ha : raw41242step1 = (fun i j => raw41242step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41242step1 raw41242step0; decide +kernel
      have hl : raw41242step1Labels = raw41242step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41242step0 raw41242step0Labels permutation101 permutation6
    mixedMoment B raw41242step1 raw41242step1Labels = mixedMoment B raw41242step2 raw41242step2Labels := by
      have ha : raw41242step2 = -raw41242step1 := by apply Matrix.ext; change ∀ i j, raw41242step2 i j = -(raw41242step1 i j); unfold raw41242step2 raw41242step1; decide +kernel
      have hl : raw41242step2Labels = raw41242step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw41243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41243step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41243step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41243 raw41243Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw41243 raw41243Labels = mixedMoment B raw41243step0 raw41243step0Labels := by
      have ha : raw41243step0 = (fun i j => raw41243 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41243step0 raw41243; decide +kernel
      have hl : raw41243step0Labels = raw41243Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41243 raw41243Labels permutation590 permutation6
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw41244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw41244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41244 raw41244Labels = mixedMoment B node4046 node4046Labels := by
  calc
    mixedMoment B raw41244 raw41244Labels = mixedMoment B raw41244step0 raw41244step0Labels := by
      have ha : raw41244step0 = (fun i j => raw41244 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41244step0 raw41244; decide +kernel
      have hl : raw41244step0Labels = raw41244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41244 raw41244Labels permutation152 permutation3
    _ = mixedMoment B node4046 node4046Labels := by rfl

def raw41245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41245 raw41245Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw41245 raw41245Labels = mixedMoment B raw41245step0 raw41245step0Labels := by
      have hz : ∀ j, raw41245 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41245step0 = (fun i j => raw41245 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41245step0 raw41245; decide +kernel
      have hl : raw41245step0Labels = raw41245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41245 raw41245Labels permutation520 hz
    mixedMoment B raw41245step0 raw41245step0Labels = mixedMoment B raw41245step1 raw41245step1Labels := by
      have ha : raw41245step1 = (fun i j => raw41245step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41245step1 raw41245step0; decide +kernel
      have hl : raw41245step1Labels = raw41245step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41245step0 raw41245step0Labels permutation149 permutation3
    mixedMoment B raw41245step1 raw41245step1Labels = mixedMoment B raw41245step2 raw41245step2Labels := by
      have ha : raw41245step2 = -raw41245step1 := by apply Matrix.ext; change ∀ i j, raw41245step2 i j = -(raw41245step1 i j); unfold raw41245step2 raw41245step1; decide +kernel
      have hl : raw41245step2Labels = raw41245step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw41246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw41246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41246 raw41246Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw41246 raw41246Labels = mixedMoment B raw41246step0 raw41246step0Labels := by
      have ha : raw41246step0 = (fun i j => raw41246 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41246step0 raw41246; decide +kernel
      have hl : raw41246step0Labels = raw41246Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41246 raw41246Labels permutation686 permutation3
    mixedMoment B raw41246step0 raw41246step0Labels = mixedMoment B raw41246step1 raw41246step1Labels := by
      have ha : raw41246step1 = -raw41246step0 := by apply Matrix.ext; change ∀ i j, raw41246step1 i j = -(raw41246step0 i j); unfold raw41246step1 raw41246step0; decide +kernel
      have hl : raw41246step1Labels = raw41246step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2720 node2720Labels := by rfl

def raw41247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw41247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41247 raw41247Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw41247 raw41247Labels = mixedMoment B raw41247step0 raw41247step0Labels := by
      have ha : raw41247step0 = (fun i j => raw41247 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41247step0 raw41247; decide +kernel
      have hl : raw41247step0Labels = raw41247Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41247 raw41247Labels permutation686 permutation3
    mixedMoment B raw41247step0 raw41247step0Labels = mixedMoment B raw41247step1 raw41247step1Labels := by
      have ha : raw41247step1 = -raw41247step0 := by apply Matrix.ext; change ∀ i j, raw41247step1 i j = -(raw41247step0 i j); unfold raw41247step1 raw41247step0; decide +kernel
      have hl : raw41247step1Labels = raw41247step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3036 node3036Labels := by rfl

def raw41248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41248 raw41248Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw41248 raw41248Labels = mixedMoment B raw41248step0 raw41248step0Labels := by
      have ha : raw41248step0 = (fun i j => raw41248 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41248step0 raw41248; decide +kernel
      have hl : raw41248step0Labels = raw41248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41248 raw41248Labels permutation686 permutation3
    mixedMoment B raw41248step0 raw41248step0Labels = mixedMoment B raw41248step1 raw41248step1Labels := by
      have ha : raw41248step1 = -raw41248step0 := by apply Matrix.ext; change ∀ i j, raw41248step1 i j = -(raw41248step0 i j); unfold raw41248step1 raw41248step0; decide +kernel
      have hl : raw41248step1Labels = raw41248step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw41249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw41249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41249 raw41249Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw41249 raw41249Labels = mixedMoment B raw41249step0 raw41249step0Labels := by
      have ha : raw41249step0 = (fun i j => raw41249 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41249step0 raw41249; decide +kernel
      have hl : raw41249step0Labels = raw41249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41249 raw41249Labels permutation686 permutation3
    mixedMoment B raw41249step0 raw41249step0Labels = mixedMoment B raw41249step1 raw41249step1Labels := by
      have ha : raw41249step1 = -raw41249step0 := by apply Matrix.ext; change ∀ i j, raw41249step1 i j = -(raw41249step0 i j); unfold raw41249step1 raw41249step0; decide +kernel
      have hl : raw41249step1Labels = raw41249step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw41250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41250 raw41250Labels = mixedMoment B node3497 node3497Labels := by
  calc
    mixedMoment B raw41250 raw41250Labels = mixedMoment B raw41250step0 raw41250step0Labels := by
      have ha : raw41250step0 = (fun i j => raw41250 (permutation532 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41250step0 raw41250; decide +kernel
      have hl : raw41250step0Labels = raw41250Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41250 raw41250Labels permutation532 permutation6
    mixedMoment B raw41250step0 raw41250step0Labels = mixedMoment B raw41250step1 raw41250step1Labels := by
      have ha : raw41250step1 = -raw41250step0 := by apply Matrix.ext; change ∀ i j, raw41250step1 i j = -(raw41250step0 i j); unfold raw41250step1 raw41250step0; decide +kernel
      have hl : raw41250step1Labels = raw41250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3497 node3497Labels := by rfl

def raw41251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw41251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41251 raw41251Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw41251 raw41251Labels = mixedMoment B raw41251step0 raw41251step0Labels := by
      have hz : ∀ j, raw41251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41251step0 = (fun i j => raw41251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41251step0 raw41251; decide +kernel
      have hl : raw41251step0Labels = raw41251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41251 raw41251Labels permutation434 hz
    mixedMoment B raw41251step0 raw41251step0Labels = mixedMoment B raw41251step1 raw41251step1Labels := by
      have ha : raw41251step1 = (fun i j => raw41251step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41251step1 raw41251step0; decide +kernel
      have hl : raw41251step1Labels = raw41251step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41251step0 raw41251step0Labels permutation128 permutation6
    _ = mixedMoment B node2879 node2879Labels := by rfl

def raw41252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41252 raw41252Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw41252 raw41252Labels = mixedMoment B raw41252step0 raw41252step0Labels := by
      have ha : raw41252step0 = (fun i j => raw41252 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41252step0 raw41252; decide +kernel
      have hl : raw41252step0Labels = raw41252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41252 raw41252Labels permutation590 permutation6
    _ = mixedMoment B node2878 node2878Labels := by rfl

def raw41253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41253 raw41253Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw41253 raw41253Labels = mixedMoment B raw41253step0 raw41253step0Labels := by
      have ha : raw41253step0 = (fun i j => raw41253 (permutation599 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41253step0 raw41253; decide +kernel
      have hl : raw41253step0Labels = raw41253Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41253 raw41253Labels permutation599 permutation6
    _ = mixedMoment B node2861 node2861Labels := by rfl

def raw41254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw41254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw41254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41254 raw41254Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw41254 raw41254Labels = mixedMoment B raw41254step0 raw41254step0Labels := by
      have hz : ∀ j, raw41254 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41254step0 = (fun i j => raw41254 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41254step0 raw41254; decide +kernel
      have hl : raw41254step0Labels = raw41254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41254 raw41254Labels permutation520 hz
    mixedMoment B raw41254step0 raw41254step0Labels = mixedMoment B raw41254step1 raw41254step1Labels := by
      have ha : raw41254step1 = (fun i j => raw41254step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41254step1 raw41254step0; decide +kernel
      have hl : raw41254step1Labels = raw41254step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41254step0 raw41254step0Labels permutation151 permutation3
    mixedMoment B raw41254step1 raw41254step1Labels = mixedMoment B raw41254step2 raw41254step2Labels := by
      have ha : raw41254step2 = -raw41254step1 := by apply Matrix.ext; change ∀ i j, raw41254step2 i j = -(raw41254step1 i j); unfold raw41254step2 raw41254step1; decide +kernel
      have hl : raw41254step2Labels = raw41254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw41255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw41255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41255 raw41255Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw41255 raw41255Labels = mixedMoment B raw41255step0 raw41255step0Labels := by
      have ha : raw41255step0 = (fun i j => raw41255 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41255step0 raw41255; decide +kernel
      have hl : raw41255step0Labels = raw41255Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41255 raw41255Labels permutation688 permutation3
    mixedMoment B raw41255step0 raw41255step0Labels = mixedMoment B raw41255step1 raw41255step1Labels := by
      have ha : raw41255step1 = -raw41255step0 := by apply Matrix.ext; change ∀ i j, raw41255step1 i j = -(raw41255step0 i j); unfold raw41255step1 raw41255step0; decide +kernel
      have hl : raw41255step1Labels = raw41255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3084 node3084Labels := by rfl

def raw41256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41256 raw41256Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw41256 raw41256Labels = mixedMoment B raw41256step0 raw41256step0Labels := by
      have ha : raw41256step0 = (fun i j => raw41256 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41256step0 raw41256; decide +kernel
      have hl : raw41256step0Labels = raw41256Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41256 raw41256Labels permutation688 permutation3
    mixedMoment B raw41256step0 raw41256step0Labels = mixedMoment B raw41256step1 raw41256step1Labels := by
      have ha : raw41256step1 = -raw41256step0 := by apply Matrix.ext; change ∀ i j, raw41256step1 i j = -(raw41256step0 i j); unfold raw41256step1 raw41256step0; decide +kernel
      have hl : raw41256step1Labels = raw41256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw41257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41257 raw41257Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw41257 raw41257Labels = mixedMoment B raw41257step0 raw41257step0Labels := by
      have ha : raw41257step0 = (fun i j => raw41257 (permutation404 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41257step0 raw41257; decide +kernel
      have hl : raw41257step0Labels = raw41257Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41257 raw41257Labels permutation404 permutation6
    mixedMoment B raw41257step0 raw41257step0Labels = mixedMoment B raw41257step1 raw41257step1Labels := by
      have ha : raw41257step1 = -raw41257step0 := by apply Matrix.ext; change ∀ i j, raw41257step1 i j = -(raw41257step0 i j); unfold raw41257step1 raw41257step0; decide +kernel
      have hl : raw41257step1Labels = raw41257step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw41258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw41258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41258 raw41258Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw41258 raw41258Labels = mixedMoment B raw41258step0 raw41258step0Labels := by
      have hz : ∀ j, raw41258 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41258step0 = (fun i j => raw41258 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41258step0 raw41258; decide +kernel
      have hl : raw41258step0Labels = raw41258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41258 raw41258Labels permutation434 hz
    mixedMoment B raw41258step0 raw41258step0Labels = mixedMoment B raw41258step1 raw41258step1Labels := by
      have ha : raw41258step1 = (fun i j => raw41258step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41258step1 raw41258step0; decide +kernel
      have hl : raw41258step1Labels = raw41258step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41258step0 raw41258step0Labels permutation129 permutation6
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw41259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41259 raw41259Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw41259 raw41259Labels = mixedMoment B raw41259step0 raw41259step0Labels := by
      have ha : raw41259step0 = (fun i j => raw41259 (permutation600 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41259step0 raw41259; decide +kernel
      have hl : raw41259step0Labels = raw41259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41259 raw41259Labels permutation600 permutation6
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw41260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw41260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw41260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41260 raw41260Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw41260 raw41260Labels = mixedMoment B raw41260step0 raw41260step0Labels := by
      have hz : ∀ j, raw41260 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41260step0 = (fun i j => raw41260 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41260step0 raw41260; decide +kernel
      have hl : raw41260step0Labels = raw41260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41260 raw41260Labels permutation520 hz
    mixedMoment B raw41260step0 raw41260step0Labels = mixedMoment B raw41260step1 raw41260step1Labels := by
      have ha : raw41260step1 = (fun i j => raw41260step0 (permutation88 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41260step1 raw41260step0; decide +kernel
      have hl : raw41260step1Labels = raw41260step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41260step0 raw41260step0Labels permutation88 permutation6
    mixedMoment B raw41260step1 raw41260step1Labels = mixedMoment B raw41260step2 raw41260step2Labels := by
      have ha : raw41260step2 = -raw41260step1 := by apply Matrix.ext; change ∀ i j, raw41260step2 i j = -(raw41260step1 i j); unfold raw41260step2 raw41260step1; decide +kernel
      have hl : raw41260step2Labels = raw41260step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw41261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41261 raw41261Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw41261 raw41261Labels = mixedMoment B raw41261step0 raw41261step0Labels := by
      have ha : raw41261step0 = (fun i j => raw41261 (permutation377 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41261step0 raw41261; decide +kernel
      have hl : raw41261step0Labels = raw41261Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41261 raw41261Labels permutation377 permutation6
    mixedMoment B raw41261step0 raw41261step0Labels = mixedMoment B raw41261step1 raw41261step1Labels := by
      have ha : raw41261step1 = -raw41261step0 := by apply Matrix.ext; change ∀ i j, raw41261step1 i j = -(raw41261step0 i j); unfold raw41261step1 raw41261step0; decide +kernel
      have hl : raw41261step1Labels = raw41261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw41262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw41262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw41262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41262 raw41262Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw41262 raw41262Labels = mixedMoment B raw41262step0 raw41262step0Labels := by
      have hz : ∀ j, raw41262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41262step0 = (fun i j => raw41262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41262step0 raw41262; decide +kernel
      have hl : raw41262step0Labels = raw41262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41262 raw41262Labels permutation434 hz
    mixedMoment B raw41262step0 raw41262step0Labels = mixedMoment B raw41262step1 raw41262step1Labels := by
      have ha : raw41262step1 = (fun i j => raw41262step0 (permutation88 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41262step1 raw41262step0; decide +kernel
      have hl : raw41262step1Labels = raw41262step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41262step0 raw41262step0Labels permutation88 permutation6
    mixedMoment B raw41262step1 raw41262step1Labels = mixedMoment B raw41262step2 raw41262step2Labels := by
      have ha : raw41262step2 = -raw41262step1 := by apply Matrix.ext; change ∀ i j, raw41262step2 i j = -(raw41262step1 i j); unfold raw41262step2 raw41262step1; decide +kernel
      have hl : raw41262step2Labels = raw41262step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw41263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw41263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw41263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41263 raw41263Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw41263 raw41263Labels = mixedMoment B raw41263step0 raw41263step0Labels := by
      have hz : ∀ j, raw41263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41263step0 = (fun i j => raw41263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41263step0 raw41263; decide +kernel
      have hl : raw41263step0Labels = raw41263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41263 raw41263Labels permutation434 hz
    mixedMoment B raw41263step0 raw41263step0Labels = mixedMoment B raw41263step1 raw41263step1Labels := by
      have ha : raw41263step1 = (fun i j => raw41263step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41263step1 raw41263step0; decide +kernel
      have hl : raw41263step1Labels = raw41263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41263step0 raw41263step0Labels permutation151 permutation3
    mixedMoment B raw41263step1 raw41263step1Labels = mixedMoment B raw41263step2 raw41263step2Labels := by
      have ha : raw41263step2 = -raw41263step1 := by apply Matrix.ext; change ∀ i j, raw41263step2 i j = -(raw41263step1 i j); unfold raw41263step2 raw41263step1; decide +kernel
      have hl : raw41263step2Labels = raw41263step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw41264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw41264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw41264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41264 raw41264Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw41264 raw41264Labels = mixedMoment B raw41264step0 raw41264step0Labels := by
      have hz : ∀ j, raw41264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41264step0 = (fun i j => raw41264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41264step0 raw41264; decide +kernel
      have hl : raw41264step0Labels = raw41264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41264 raw41264Labels permutation434 hz
    mixedMoment B raw41264step0 raw41264step0Labels = mixedMoment B raw41264step1 raw41264step1Labels := by
      have ha : raw41264step1 = (fun i j => raw41264step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41264step1 raw41264step0; decide +kernel
      have hl : raw41264step1Labels = raw41264step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41264step0 raw41264step0Labels permutation115 permutation6
    mixedMoment B raw41264step1 raw41264step1Labels = mixedMoment B raw41264step2 raw41264step2Labels := by
      have ha : raw41264step2 = -raw41264step1 := by apply Matrix.ext; change ∀ i j, raw41264step2 i j = -(raw41264step1 i j); unfold raw41264step2 raw41264step1; decide +kernel
      have hl : raw41264step2Labels = raw41264step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw41265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw41265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw41265step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41265 raw41265Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw41265 raw41265Labels = mixedMoment B raw41265step0 raw41265step0Labels := by
      have hz : ∀ j, raw41265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41265step0 = (fun i j => raw41265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41265step0 raw41265; decide +kernel
      have hl : raw41265step0Labels = raw41265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41265 raw41265Labels permutation434 hz
    mixedMoment B raw41265step0 raw41265step0Labels = mixedMoment B raw41265step1 raw41265step1Labels := by
      have ha : raw41265step1 = (fun i j => raw41265step0 (permutation112 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41265step1 raw41265step0; decide +kernel
      have hl : raw41265step1Labels = raw41265step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41265step0 raw41265step0Labels permutation112 permutation6
    mixedMoment B raw41265step1 raw41265step1Labels = mixedMoment B raw41265step2 raw41265step2Labels := by
      have ha : raw41265step2 = -raw41265step1 := by apply Matrix.ext; change ∀ i j, raw41265step2 i j = -(raw41265step1 i j); unfold raw41265step2 raw41265step1; decide +kernel
      have hl : raw41265step2Labels = raw41265step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw41266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw41266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41266step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41266 raw41266Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw41266 raw41266Labels = mixedMoment B raw41266step0 raw41266step0Labels := by
      have hz : ∀ j, raw41266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41266step0 = (fun i j => raw41266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41266step0 raw41266; decide +kernel
      have hl : raw41266step0Labels = raw41266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41266 raw41266Labels permutation434 hz
    mixedMoment B raw41266step0 raw41266step0Labels = mixedMoment B raw41266step1 raw41266step1Labels := by
      have ha : raw41266step1 = (fun i j => raw41266step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41266step1 raw41266step0; decide +kernel
      have hl : raw41266step1Labels = raw41266step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41266step0 raw41266step0Labels permutation139 permutation6
    mixedMoment B raw41266step1 raw41266step1Labels = mixedMoment B raw41266step2 raw41266step2Labels := by
      have ha : raw41266step2 = -raw41266step1 := by apply Matrix.ext; change ∀ i j, raw41266step2 i j = -(raw41266step1 i j); unfold raw41266step2 raw41266step1; decide +kernel
      have hl : raw41266step2Labels = raw41266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw41267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw41267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41267 raw41267Labels = mixedMoment B node4047 node4047Labels := by
  calc
    mixedMoment B raw41267 raw41267Labels = mixedMoment B raw41267step0 raw41267step0Labels := by
      have hz : ∀ j, raw41267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41267step0 = (fun i j => raw41267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41267step0 raw41267; decide +kernel
      have hl : raw41267step0Labels = raw41267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41267 raw41267Labels permutation434 hz
    mixedMoment B raw41267step0 raw41267step0Labels = mixedMoment B raw41267step1 raw41267step1Labels := by
      have ha : raw41267step1 = (fun i j => raw41267step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41267step1 raw41267step0; decide +kernel
      have hl : raw41267step1Labels = raw41267step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41267step0 raw41267step0Labels permutation151 permutation3
    mixedMoment B raw41267step1 raw41267step1Labels = mixedMoment B raw41267step2 raw41267step2Labels := by
      have ha : raw41267step2 = -raw41267step1 := by apply Matrix.ext; change ∀ i j, raw41267step2 i j = -(raw41267step1 i j); unfold raw41267step2 raw41267step1; decide +kernel
      have hl : raw41267step2Labels = raw41267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4047 node4047Labels := by rfl

def raw41268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw41268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41268 raw41268Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw41268 raw41268Labels = mixedMoment B raw41268step0 raw41268step0Labels := by
      have ha : raw41268step0 = (fun i j => raw41268 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41268step0 raw41268; decide +kernel
      have hl : raw41268step0Labels = raw41268Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41268 raw41268Labels permutation664 permutation3
    mixedMoment B raw41268step0 raw41268step0Labels = mixedMoment B raw41268step1 raw41268step1Labels := by
      have ha : raw41268step1 = -raw41268step0 := by apply Matrix.ext; change ∀ i j, raw41268step1 i j = -(raw41268step0 i j); unfold raw41268step1 raw41268step0; decide +kernel
      have hl : raw41268step1Labels = raw41268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4008 node4008Labels := by rfl

def raw41269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41269 raw41269Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw41269 raw41269Labels = mixedMoment B raw41269step0 raw41269step0Labels := by
      have ha : raw41269step0 = (fun i j => raw41269 (permutation556 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41269step0 raw41269; decide +kernel
      have hl : raw41269step0Labels = raw41269Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41269 raw41269Labels permutation556 permutation6
    mixedMoment B raw41269step0 raw41269step0Labels = mixedMoment B raw41269step1 raw41269step1Labels := by
      have ha : raw41269step1 = -raw41269step0 := by apply Matrix.ext; change ∀ i j, raw41269step1 i j = -(raw41269step0 i j); unfold raw41269step1 raw41269step0; decide +kernel
      have hl : raw41269step1Labels = raw41269step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw41270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41270 raw41270Labels = mixedMoment B node4044 node4044Labels := by
  calc
    mixedMoment B raw41270 raw41270Labels = mixedMoment B raw41270step0 raw41270step0Labels := by
      have ha : raw41270step0 = (fun i j => raw41270 (permutation188 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41270step0 raw41270; decide +kernel
      have hl : raw41270step0Labels = raw41270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41270 raw41270Labels permutation188 permutation6
    _ = mixedMoment B node4044 node4044Labels := by rfl

def raw41271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw41271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41271 raw41271Labels = mixedMoment B node4046 node4046Labels := by
  calc
    mixedMoment B raw41271 raw41271Labels = mixedMoment B raw41271step0 raw41271step0Labels := by
      have ha : raw41271step0 = (fun i j => raw41271 (permutation192 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41271step0 raw41271; decide +kernel
      have hl : raw41271step0Labels = raw41271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41271 raw41271Labels permutation192 permutation6
    _ = mixedMoment B node4046 node4046Labels := by rfl

def raw41272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41272 raw41272Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw41272 raw41272Labels = mixedMoment B raw41272step0 raw41272step0Labels := by
      have ha : raw41272step0 = (fun i j => raw41272 (permutation466 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41272step0 raw41272; decide +kernel
      have hl : raw41272step0Labels = raw41272Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41272 raw41272Labels permutation466 permutation6
    mixedMoment B raw41272step0 raw41272step0Labels = mixedMoment B raw41272step1 raw41272step1Labels := by
      have ha : raw41272step1 = -raw41272step0 := by apply Matrix.ext; change ∀ i j, raw41272step1 i j = -(raw41272step0 i j); unfold raw41272step1 raw41272step0; decide +kernel
      have hl : raw41272step1Labels = raw41272step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw41273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41273 raw41273Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw41273 raw41273Labels = mixedMoment B raw41273step0 raw41273step0Labels := by
      have hz : ∀ j, raw41273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41273step0 = (fun i j => raw41273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41273step0 raw41273; decide +kernel
      have hl : raw41273step0Labels = raw41273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41273 raw41273Labels permutation346 hz
    mixedMoment B raw41273step0 raw41273step0Labels = mixedMoment B raw41273step1 raw41273step1Labels := by
      have ha : raw41273step1 = (fun i j => raw41273step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41273step1 raw41273step0; decide +kernel
      have hl : raw41273step1Labels = raw41273step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41273step0 raw41273step0Labels permutation128 permutation6
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw41274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41274 raw41274Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw41274 raw41274Labels = mixedMoment B raw41274step0 raw41274step0Labels := by
      have hz : ∀ j, raw41274 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41274step0 = (fun i j => raw41274 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41274step0 raw41274; decide +kernel
      have hl : raw41274step0Labels = raw41274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41274 raw41274Labels permutation346 hz
    mixedMoment B raw41274step0 raw41274step0Labels = mixedMoment B raw41274step1 raw41274step1Labels := by
      have ha : raw41274step1 = (fun i j => raw41274step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41274step1 raw41274step0; decide +kernel
      have hl : raw41274step1Labels = raw41274step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41274step0 raw41274step0Labels permutation104 permutation6
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw41275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw41275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw41275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41275 raw41275Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw41275 raw41275Labels = mixedMoment B raw41275step0 raw41275step0Labels := by
      have hz : ∀ j, raw41275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41275step0 = (fun i j => raw41275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41275step0 raw41275; decide +kernel
      have hl : raw41275step0Labels = raw41275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41275 raw41275Labels permutation346 hz
    mixedMoment B raw41275step0 raw41275step0Labels = mixedMoment B raw41275step1 raw41275step1Labels := by
      have ha : raw41275step1 = (fun i j => raw41275step0 (permutation90 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41275step1 raw41275step0; decide +kernel
      have hl : raw41275step1Labels = raw41275step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41275step0 raw41275step0Labels permutation90 permutation6
    mixedMoment B raw41275step1 raw41275step1Labels = mixedMoment B raw41275step2 raw41275step2Labels := by
      have ha : raw41275step2 = -raw41275step1 := by apply Matrix.ext; change ∀ i j, raw41275step2 i j = -(raw41275step1 i j); unfold raw41275step2 raw41275step1; decide +kernel
      have hl : raw41275step2Labels = raw41275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw41276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41276 raw41276Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw41276 raw41276Labels = mixedMoment B raw41276step0 raw41276step0Labels := by
      have ha : raw41276step0 = (fun i j => raw41276 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41276step0 raw41276; decide +kernel
      have hl : raw41276step0Labels = raw41276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41276 raw41276Labels permutation590 permutation6
    _ = mixedMoment B node2880 node2880Labels := by rfl

def raw41277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41277 raw41277Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw41277 raw41277Labels = mixedMoment B raw41277step0 raw41277step0Labels := by
      have ha : raw41277step0 = (fun i j => raw41277 (permutation526 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41277step0 raw41277; decide +kernel
      have hl : raw41277step0Labels = raw41277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41277 raw41277Labels permutation526 permutation6
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw41278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw41278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw41278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw41278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw41278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41278 raw41278Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw41278 raw41278Labels = mixedMoment B raw41278step0 raw41278step0Labels := by
      have hz : ∀ j, raw41278 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41278step0 = (fun i j => raw41278 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41278step0 raw41278; decide +kernel
      have hl : raw41278step0Labels = raw41278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41278 raw41278Labels permutation520 hz
    mixedMoment B raw41278step0 raw41278step0Labels = mixedMoment B raw41278step1 raw41278step1Labels := by
      have ha : raw41278step1 = (fun i j => raw41278step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41278step1 raw41278step0; decide +kernel
      have hl : raw41278step1Labels = raw41278step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41278step0 raw41278step0Labels permutation149 permutation3
    mixedMoment B raw41278step1 raw41278step1Labels = mixedMoment B raw41278step2 raw41278step2Labels := by
      have ha : raw41278step2 = -raw41278step1 := by apply Matrix.ext; change ∀ i j, raw41278step2 i j = -(raw41278step1 i j); unfold raw41278step2 raw41278step1; decide +kernel
      have hl : raw41278step2Labels = raw41278step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3108 node3108Labels := by rfl

def raw41279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41279 raw41279Labels = mixedMoment B node3922 node3922Labels := by
  calc
    mixedMoment B raw41279 raw41279Labels = mixedMoment B raw41279step0 raw41279step0Labels := by
      have ha : raw41279step0 = (fun i j => raw41279 (permutation300 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41279step0 raw41279; decide +kernel
      have hl : raw41279step0Labels = raw41279Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41279 raw41279Labels permutation300 permutation6
    mixedMoment B raw41279step0 raw41279step0Labels = mixedMoment B raw41279step1 raw41279step1Labels := by
      have ha : raw41279step1 = -raw41279step0 := by apply Matrix.ext; change ∀ i j, raw41279step1 i j = -(raw41279step0 i j); unfold raw41279step1 raw41279step0; decide +kernel
      have hl : raw41279step1Labels = raw41279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3922 node3922Labels := by rfl

def raw41280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41280 raw41280Labels = mixedMoment B node2868 node2868Labels := by
  calc
    mixedMoment B raw41280 raw41280Labels = mixedMoment B raw41280step0 raw41280step0Labels := by
      have hz : ∀ j, raw41280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41280step0 = (fun i j => raw41280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41280step0 raw41280; decide +kernel
      have hl : raw41280step0Labels = raw41280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41280 raw41280Labels permutation434 hz
    mixedMoment B raw41280step0 raw41280step0Labels = mixedMoment B raw41280step1 raw41280step1Labels := by
      have ha : raw41280step1 = (fun i j => raw41280step0 (permutation132 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41280step1 raw41280step0; decide +kernel
      have hl : raw41280step1Labels = raw41280step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41280step0 raw41280step0Labels permutation132 permutation6
    _ = mixedMoment B node2868 node2868Labels := by rfl

def raw41281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw41281step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0]]
def raw41281step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw41281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41281step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw41281step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41281 raw41281Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw41281 raw41281Labels = mixedMoment B raw41281step0 raw41281step0Labels := by
      have hz : ∀ j, raw41281 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41281step0 = (fun i j => raw41281 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41281step0 raw41281; decide +kernel
      have hl : raw41281step0Labels = raw41281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41281 raw41281Labels permutation520 hz
    mixedMoment B raw41281step0 raw41281step0Labels = mixedMoment B raw41281step1 raw41281step1Labels := by
      have hz : ∀ j, raw41281step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41281step1 = (fun i j => raw41281step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41281step1 raw41281step0; decide +kernel
      have hl : raw41281step1Labels = raw41281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41281step0 raw41281step0Labels permutation104 hz
    mixedMoment B raw41281step1 raw41281step1Labels = mixedMoment B raw41281step2 raw41281step2Labels := by
      have ha : raw41281step2 = (fun i j => raw41281step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41281step2 raw41281step1; decide +kernel
      have hl : raw41281step2Labels = raw41281step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41281step1 raw41281step1Labels permutation31 permutation3
    mixedMoment B raw41281step2 raw41281step2Labels = mixedMoment B raw41281step3 raw41281step3Labels := by
      have ha : raw41281step3 = -raw41281step2 := by apply Matrix.ext; change ∀ i j, raw41281step3 i j = -(raw41281step2 i j); unfold raw41281step3 raw41281step2; decide +kernel
      have hl : raw41281step3Labels = raw41281step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw41282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw41282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41282 raw41282Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw41282 raw41282Labels = mixedMoment B raw41282step0 raw41282step0Labels := by
      have hz : ∀ j, raw41282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41282step0 = (fun i j => raw41282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41282step0 raw41282; decide +kernel
      have hl : raw41282step0Labels = raw41282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41282 raw41282Labels permutation434 hz
    mixedMoment B raw41282step0 raw41282step0Labels = mixedMoment B raw41282step1 raw41282step1Labels := by
      have ha : raw41282step1 = (fun i j => raw41282step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41282step1 raw41282step0; decide +kernel
      have hl : raw41282step1Labels = raw41282step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41282step0 raw41282step0Labels permutation73 permutation6
    mixedMoment B raw41282step1 raw41282step1Labels = mixedMoment B raw41282step2 raw41282step2Labels := by
      have ha : raw41282step2 = -raw41282step1 := by apply Matrix.ext; change ∀ i j, raw41282step2 i j = -(raw41282step1 i j); unfold raw41282step2 raw41282step1; decide +kernel
      have hl : raw41282step2Labels = raw41282step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw41283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw41283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41283 raw41283Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw41283 raw41283Labels = mixedMoment B raw41283step0 raw41283step0Labels := by
      have hz : ∀ j, raw41283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41283step0 = (fun i j => raw41283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41283step0 raw41283; decide +kernel
      have hl : raw41283step0Labels = raw41283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41283 raw41283Labels permutation434 hz
    mixedMoment B raw41283step0 raw41283step0Labels = mixedMoment B raw41283step1 raw41283step1Labels := by
      have ha : raw41283step1 = (fun i j => raw41283step0 (permutation112 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41283step1 raw41283step0; decide +kernel
      have hl : raw41283step1Labels = raw41283step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41283step0 raw41283step0Labels permutation112 permutation6
    mixedMoment B raw41283step1 raw41283step1Labels = mixedMoment B raw41283step2 raw41283step2Labels := by
      have ha : raw41283step2 = -raw41283step1 := by apply Matrix.ext; change ∀ i j, raw41283step2 i j = -(raw41283step1 i j); unfold raw41283step2 raw41283step1; decide +kernel
      have hl : raw41283step2Labels = raw41283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw41284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41284 raw41284Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw41284 raw41284Labels = mixedMoment B raw41284step0 raw41284step0Labels := by
      have hz : ∀ j, raw41284 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41284step0 = (fun i j => raw41284 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41284step0 raw41284; decide +kernel
      have hl : raw41284step0Labels = raw41284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41284 raw41284Labels permutation434 hz
    mixedMoment B raw41284step0 raw41284step0Labels = mixedMoment B raw41284step1 raw41284step1Labels := by
      have ha : raw41284step1 = (fun i j => raw41284step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41284step1 raw41284step0; decide +kernel
      have hl : raw41284step1Labels = raw41284step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41284step0 raw41284step0Labels permutation79 permutation6
    mixedMoment B raw41284step1 raw41284step1Labels = mixedMoment B raw41284step2 raw41284step2Labels := by
      have ha : raw41284step2 = -raw41284step1 := by apply Matrix.ext; change ∀ i j, raw41284step2 i j = -(raw41284step1 i j); unfold raw41284step2 raw41284step1; decide +kernel
      have hl : raw41284step2Labels = raw41284step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw41285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41285 raw41285Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw41285 raw41285Labels = mixedMoment B raw41285step0 raw41285step0Labels := by
      have hz : ∀ j, raw41285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41285step0 = (fun i j => raw41285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41285step0 raw41285; decide +kernel
      have hl : raw41285step0Labels = raw41285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41285 raw41285Labels permutation434 hz
    mixedMoment B raw41285step0 raw41285step0Labels = mixedMoment B raw41285step1 raw41285step1Labels := by
      have ha : raw41285step1 = (fun i j => raw41285step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41285step1 raw41285step0; decide +kernel
      have hl : raw41285step1Labels = raw41285step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41285step0 raw41285step0Labels permutation73 permutation6
    mixedMoment B raw41285step1 raw41285step1Labels = mixedMoment B raw41285step2 raw41285step2Labels := by
      have ha : raw41285step2 = -raw41285step1 := by apply Matrix.ext; change ∀ i j, raw41285step2 i j = -(raw41285step1 i j); unfold raw41285step2 raw41285step1; decide +kernel
      have hl : raw41285step2Labels = raw41285step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw41286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41286 raw41286Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw41286 raw41286Labels = mixedMoment B raw41286step0 raw41286step0Labels := by
      have ha : raw41286step0 = (fun i j => raw41286 (permutation315 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41286step0 raw41286; decide +kernel
      have hl : raw41286step0Labels = raw41286Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41286 raw41286Labels permutation315 permutation6
    mixedMoment B raw41286step0 raw41286step0Labels = mixedMoment B raw41286step1 raw41286step1Labels := by
      have ha : raw41286step1 = -raw41286step0 := by apply Matrix.ext; change ∀ i j, raw41286step1 i j = -(raw41286step0 i j); unfold raw41286step1 raw41286step0; decide +kernel
      have hl : raw41286step1Labels = raw41286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

def raw41287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41287 raw41287Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw41287 raw41287Labels = mixedMoment B raw41287step0 raw41287step0Labels := by
      have ha : raw41287step0 = (fun i j => raw41287 (permutation321 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41287step0 raw41287; decide +kernel
      have hl : raw41287step0Labels = raw41287Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41287 raw41287Labels permutation321 permutation6
    mixedMoment B raw41287step0 raw41287step0Labels = mixedMoment B raw41287step1 raw41287step1Labels := by
      have ha : raw41287step1 = -raw41287step0 := by apply Matrix.ext; change ∀ i j, raw41287step1 i j = -(raw41287step0 i j); unfold raw41287step1 raw41287step0; decide +kernel
      have hl : raw41287step1Labels = raw41287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw41288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41288 raw41288Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw41288 raw41288Labels = mixedMoment B raw41288step0 raw41288step0Labels := by
      have ha : raw41288step0 = (fun i j => raw41288 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41288step0 raw41288; decide +kernel
      have hl : raw41288step0Labels = raw41288Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41288 raw41288Labels permutation463 permutation6
    mixedMoment B raw41288step0 raw41288step0Labels = mixedMoment B raw41288step1 raw41288step1Labels := by
      have ha : raw41288step1 = -raw41288step0 := by apply Matrix.ext; change ∀ i j, raw41288step1 i j = -(raw41288step0 i j); unfold raw41288step1 raw41288step0; decide +kernel
      have hl : raw41288step1Labels = raw41288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3703 node3703Labels := by rfl

def raw41289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -2, 2], ![2, 1, -3]]
def raw41289step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw41289step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41289 raw41289Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw41289 raw41289Labels = mixedMoment B raw41289step0 raw41289step0Labels := by
      have hz : ∀ j, raw41289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41289step0 = (fun i j => raw41289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41289step0 raw41289; decide +kernel
      have hl : raw41289step0Labels = raw41289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41289 raw41289Labels permutation434 hz
    mixedMoment B raw41289step0 raw41289step0Labels = mixedMoment B raw41289step1 raw41289step1Labels := by
      have hz : ∀ j, raw41289step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41289step1 = (fun i j => raw41289step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41289step1 raw41289step0; decide +kernel
      have hl : raw41289step1Labels = raw41289step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41289step0 raw41289step0Labels permutation80 hz
    mixedMoment B raw41289step1 raw41289step1Labels = mixedMoment B raw41289step2 raw41289step2Labels := by
      have ha : raw41289step2 = (fun i j => raw41289step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41289step2 raw41289step1; decide +kernel
      have hl : raw41289step2Labels = raw41289step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41289step1 raw41289step1Labels permutation26 permutation6
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw41290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41290step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![1, 1, -2], ![1, -2, 1]]
def raw41290step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw41290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41290 raw41290Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw41290 raw41290Labels = mixedMoment B raw41290step0 raw41290step0Labels := by
      have hz : ∀ j, raw41290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41290step0 = (fun i j => raw41290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41290step0 raw41290; decide +kernel
      have hl : raw41290step0Labels = raw41290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41290 raw41290Labels permutation434 hz
    mixedMoment B raw41290step0 raw41290step0Labels = mixedMoment B raw41290step1 raw41290step1Labels := by
      have hz : ∀ j, raw41290step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41290step1 = (fun i j => raw41290step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41290step1 raw41290step0; decide +kernel
      have hl : raw41290step1Labels = raw41290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41290step0 raw41290step0Labels permutation80 hz
    mixedMoment B raw41290step1 raw41290step1Labels = mixedMoment B raw41290step2 raw41290step2Labels := by
      have ha : raw41290step2 = (fun i j => raw41290step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41290step2 raw41290step1; decide +kernel
      have hl : raw41290step2Labels = raw41290step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41290step1 raw41290step1Labels permutation21 permutation6
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw41291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41291step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41291step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41291 raw41291Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw41291 raw41291Labels = mixedMoment B raw41291step0 raw41291step0Labels := by
      have hz : ∀ j, raw41291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41291step0 = (fun i j => raw41291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41291step0 raw41291; decide +kernel
      have hl : raw41291step0Labels = raw41291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41291 raw41291Labels permutation346 hz
    mixedMoment B raw41291step0 raw41291step0Labels = mixedMoment B raw41291step1 raw41291step1Labels := by
      have ha : raw41291step1 = (fun i j => raw41291step0 (permutation131 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41291step1 raw41291step0; decide +kernel
      have hl : raw41291step1Labels = raw41291step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41291step0 raw41291step0Labels permutation131 permutation6
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw41292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41292 raw41292Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw41292 raw41292Labels = mixedMoment B raw41292step0 raw41292step0Labels := by
      have hz : ∀ j, raw41292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41292step0 = (fun i j => raw41292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41292step0 raw41292; decide +kernel
      have hl : raw41292step0Labels = raw41292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41292 raw41292Labels permutation346 hz
    mixedMoment B raw41292step0 raw41292step0Labels = mixedMoment B raw41292step1 raw41292step1Labels := by
      have ha : raw41292step1 = (fun i j => raw41292step0 (permutation109 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41292step1 raw41292step0; decide +kernel
      have hl : raw41292step1Labels = raw41292step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41292step0 raw41292step0Labels permutation109 permutation6
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw41293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw41293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41293step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41293 raw41293Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw41293 raw41293Labels = mixedMoment B raw41293step0 raw41293step0Labels := by
      have hz : ∀ j, raw41293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41293step0 = (fun i j => raw41293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41293step0 raw41293; decide +kernel
      have hl : raw41293step0Labels = raw41293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41293 raw41293Labels permutation346 hz
    mixedMoment B raw41293step0 raw41293step0Labels = mixedMoment B raw41293step1 raw41293step1Labels := by
      have ha : raw41293step1 = (fun i j => raw41293step0 (permutation90 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41293step1 raw41293step0; decide +kernel
      have hl : raw41293step1Labels = raw41293step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41293step0 raw41293step0Labels permutation90 permutation6
    mixedMoment B raw41293step1 raw41293step1Labels = mixedMoment B raw41293step2 raw41293step2Labels := by
      have ha : raw41293step2 = -raw41293step1 := by apply Matrix.ext; change ∀ i j, raw41293step2 i j = -(raw41293step1 i j); unfold raw41293step2 raw41293step1; decide +kernel
      have hl : raw41293step2Labels = raw41293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw41294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41294 raw41294Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw41294 raw41294Labels = mixedMoment B raw41294step0 raw41294step0Labels := by
      have ha : raw41294step0 = (fun i j => raw41294 (permutation528 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41294step0 raw41294; decide +kernel
      have hl : raw41294step0Labels = raw41294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41294 raw41294Labels permutation528 permutation6
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw41295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw41295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1]]
def raw41295step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw41295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41295step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41295 raw41295Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw41295 raw41295Labels = mixedMoment B raw41295step0 raw41295step0Labels := by
      have hz : ∀ j, raw41295 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41295step0 = (fun i j => raw41295 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41295step0 raw41295; decide +kernel
      have hl : raw41295step0Labels = raw41295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41295 raw41295Labels permutation520 hz
    mixedMoment B raw41295step0 raw41295step0Labels = mixedMoment B raw41295step1 raw41295step1Labels := by
      have hz : ∀ j, raw41295step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41295step1 = (fun i j => raw41295step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41295step1 raw41295step0; decide +kernel
      have hl : raw41295step1Labels = raw41295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41295step0 raw41295step0Labels permutation104 hz
    mixedMoment B raw41295step1 raw41295step1Labels = mixedMoment B raw41295step2 raw41295step2Labels := by
      have ha : raw41295step2 = (fun i j => raw41295step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41295step2 raw41295step1; decide +kernel
      have hl : raw41295step2Labels = raw41295step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41295step1 raw41295step1Labels permutation19 permutation6
    mixedMoment B raw41295step2 raw41295step2Labels = mixedMoment B raw41295step3 raw41295step3Labels := by
      have ha : raw41295step3 = -raw41295step2 := by apply Matrix.ext; change ∀ i j, raw41295step3 i j = -(raw41295step2 i j); unfold raw41295step3 raw41295step2; decide +kernel
      have hl : raw41295step3Labels = raw41295step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw41296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41296 raw41296Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw41296 raw41296Labels = mixedMoment B raw41296step0 raw41296step0Labels := by
      have hz : ∀ j, raw41296 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41296step0 = (fun i j => raw41296 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41296step0 raw41296; decide +kernel
      have hl : raw41296step0Labels = raw41296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41296 raw41296Labels permutation434 hz
    mixedMoment B raw41296step0 raw41296step0Labels = mixedMoment B raw41296step1 raw41296step1Labels := by
      have ha : raw41296step1 = (fun i j => raw41296step0 (permutation70 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41296step1 raw41296step0; decide +kernel
      have hl : raw41296step1Labels = raw41296step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41296step0 raw41296step0Labels permutation70 permutation6
    mixedMoment B raw41296step1 raw41296step1Labels = mixedMoment B raw41296step2 raw41296step2Labels := by
      have ha : raw41296step2 = -raw41296step1 := by apply Matrix.ext; change ∀ i j, raw41296step2 i j = -(raw41296step1 i j); unfold raw41296step2 raw41296step1; decide +kernel
      have hl : raw41296step2Labels = raw41296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw41297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41297 raw41297Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw41297 raw41297Labels = mixedMoment B raw41297step0 raw41297step0Labels := by
      have hz : ∀ j, raw41297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41297step0 = (fun i j => raw41297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41297step0 raw41297; decide +kernel
      have hl : raw41297step0Labels = raw41297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41297 raw41297Labels permutation434 hz
    mixedMoment B raw41297step0 raw41297step0Labels = mixedMoment B raw41297step1 raw41297step1Labels := by
      have ha : raw41297step1 = (fun i j => raw41297step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41297step1 raw41297step0; decide +kernel
      have hl : raw41297step1Labels = raw41297step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41297step0 raw41297step0Labels permutation79 permutation6
    mixedMoment B raw41297step1 raw41297step1Labels = mixedMoment B raw41297step2 raw41297step2Labels := by
      have ha : raw41297step2 = -raw41297step1 := by apply Matrix.ext; change ∀ i j, raw41297step2 i j = -(raw41297step1 i j); unfold raw41297step2 raw41297step1; decide +kernel
      have hl : raw41297step2Labels = raw41297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw41298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41298step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41298step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41298 raw41298Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw41298 raw41298Labels = mixedMoment B raw41298step0 raw41298step0Labels := by
      have ha : raw41298step0 = (fun i j => raw41298 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41298step0 raw41298; decide +kernel
      have hl : raw41298step0Labels = raw41298Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41298 raw41298Labels permutation317 permutation6
    mixedMoment B raw41298step0 raw41298step0Labels = mixedMoment B raw41298step1 raw41298step1Labels := by
      have ha : raw41298step1 = -raw41298step0 := by apply Matrix.ext; change ∀ i j, raw41298step1 i j = -(raw41298step0 i j); unfold raw41298step1 raw41298step0; decide +kernel
      have hl : raw41298step1Labels = raw41298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw41299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, -1, 1], ![2, 1, -3]]
def raw41299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw41299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41299step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41299step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41299 raw41299Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw41299 raw41299Labels = mixedMoment B raw41299step0 raw41299step0Labels := by
      have hz : ∀ j, raw41299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41299step0 = (fun i j => raw41299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41299step0 raw41299; decide +kernel
      have hl : raw41299step0Labels = raw41299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41299 raw41299Labels permutation434 hz
    mixedMoment B raw41299step0 raw41299step0Labels = mixedMoment B raw41299step1 raw41299step1Labels := by
      have hz : ∀ j, raw41299step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41299step1 = (fun i j => raw41299step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41299step1 raw41299step0; decide +kernel
      have hl : raw41299step1Labels = raw41299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41299step0 raw41299step0Labels permutation80 hz
    mixedMoment B raw41299step1 raw41299step1Labels = mixedMoment B raw41299step2 raw41299step2Labels := by
      have ha : raw41299step2 = (fun i j => raw41299step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41299step2 raw41299step1; decide +kernel
      have hl : raw41299step2Labels = raw41299step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41299step1 raw41299step1Labels permutation16 permutation6
    mixedMoment B raw41299step2 raw41299step2Labels = mixedMoment B raw41299step3 raw41299step3Labels := by
      have ha : raw41299step3 = -raw41299step2 := by apply Matrix.ext; change ∀ i j, raw41299step3 i j = -(raw41299step2 i j); unfold raw41299step3 raw41299step2; decide +kernel
      have hl : raw41299step3Labels = raw41299step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw41300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![1, 1, -2], ![1, -1, 0]]
def raw41300step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41300step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41300 raw41300Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw41300 raw41300Labels = mixedMoment B raw41300step0 raw41300step0Labels := by
      have hz : ∀ j, raw41300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41300step0 = (fun i j => raw41300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41300step0 raw41300; decide +kernel
      have hl : raw41300step0Labels = raw41300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41300 raw41300Labels permutation434 hz
    mixedMoment B raw41300step0 raw41300step0Labels = mixedMoment B raw41300step1 raw41300step1Labels := by
      have hz : ∀ j, raw41300step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41300step1 = (fun i j => raw41300step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41300step1 raw41300step0; decide +kernel
      have hl : raw41300step1Labels = raw41300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41300step0 raw41300step0Labels permutation80 hz
    mixedMoment B raw41300step1 raw41300step1Labels = mixedMoment B raw41300step2 raw41300step2Labels := by
      have ha : raw41300step2 = (fun i j => raw41300step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41300step2 raw41300step1; decide +kernel
      have hl : raw41300step2Labels = raw41300step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41300step1 raw41300step1Labels permutation18 permutation6
    mixedMoment B raw41300step2 raw41300step2Labels = mixedMoment B raw41300step3 raw41300step3Labels := by
      have ha : raw41300step3 = -raw41300step2 := by apply Matrix.ext; change ∀ i j, raw41300step3 i j = -(raw41300step2 i j); unfold raw41300step3 raw41300step2; decide +kernel
      have hl : raw41300step3Labels = raw41300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw41301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw41301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41301 raw41301Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw41301 raw41301Labels = mixedMoment B raw41301step0 raw41301step0Labels := by
      have hz : ∀ j, raw41301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41301step0 = (fun i j => raw41301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41301step0 raw41301; decide +kernel
      have hl : raw41301step0Labels = raw41301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41301 raw41301Labels permutation346 hz
    mixedMoment B raw41301step0 raw41301step0Labels = mixedMoment B raw41301step1 raw41301step1Labels := by
      have ha : raw41301step1 = (fun i j => raw41301step0 (permutation66 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41301step1 raw41301step0; decide +kernel
      have hl : raw41301step1Labels = raw41301step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41301step0 raw41301step0Labels permutation66 permutation6
    mixedMoment B raw41301step1 raw41301step1Labels = mixedMoment B raw41301step2 raw41301step2Labels := by
      have ha : raw41301step2 = -raw41301step1 := by apply Matrix.ext; change ∀ i j, raw41301step2 i j = -(raw41301step1 i j); unfold raw41301step2 raw41301step1; decide +kernel
      have hl : raw41301step2Labels = raw41301step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw41302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![2, 0, -2]]
def raw41302step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41302step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41302 raw41302Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw41302 raw41302Labels = mixedMoment B raw41302step0 raw41302step0Labels := by
      have hz : ∀ j, raw41302 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41302step0 = (fun i j => raw41302 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41302step0 raw41302; decide +kernel
      have hl : raw41302step0Labels = raw41302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41302 raw41302Labels permutation520 hz
    mixedMoment B raw41302step0 raw41302step0Labels = mixedMoment B raw41302step1 raw41302step1Labels := by
      have hz : ∀ j, raw41302step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41302step1 = (fun i j => raw41302step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41302step1 raw41302step0; decide +kernel
      have hl : raw41302step1Labels = raw41302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41302step0 raw41302step0Labels permutation104 hz
    mixedMoment B raw41302step1 raw41302step1Labels = mixedMoment B raw41302step2 raw41302step2Labels := by
      have ha : raw41302step2 = (fun i j => raw41302step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41302step2 raw41302step1; decide +kernel
      have hl : raw41302step2Labels = raw41302step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41302step1 raw41302step1Labels permutation16 permutation6
    mixedMoment B raw41302step2 raw41302step2Labels = mixedMoment B raw41302step3 raw41302step3Labels := by
      have ha : raw41302step3 = -raw41302step2 := by apply Matrix.ext; change ∀ i j, raw41302step3 i j = -(raw41302step2 i j); unfold raw41302step3 raw41302step2; decide +kernel
      have hl : raw41302step3Labels = raw41302step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw41303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![2, 1, -3]]
def raw41303step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41303step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![2, 1, -3]]
def raw41303step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41303step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw41303step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41303step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw41303step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41303 raw41303Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw41303 raw41303Labels = mixedMoment B raw41303step0 raw41303step0Labels := by
      have hz : ∀ j, raw41303 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41303step0 = (fun i j => raw41303 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41303step0 raw41303; decide +kernel
      have hl : raw41303step0Labels = raw41303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41303 raw41303Labels permutation520 hz
    mixedMoment B raw41303step0 raw41303step0Labels = mixedMoment B raw41303step1 raw41303step1Labels := by
      have hz : ∀ j, raw41303step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41303step1 = (fun i j => raw41303step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41303step1 raw41303step0; decide +kernel
      have hl : raw41303step1Labels = raw41303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41303step0 raw41303step0Labels permutation104 hz
    mixedMoment B raw41303step1 raw41303step1Labels = mixedMoment B raw41303step2 raw41303step2Labels := by
      have hz : ∀ j, raw41303step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41303step2 = (fun i j => raw41303step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41303step2 raw41303step1; decide +kernel
      have hl : raw41303step2Labels = raw41303step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41303step1 raw41303step1Labels permutation20 hz
    mixedMoment B raw41303step2 raw41303step2Labels = mixedMoment B raw41303step3 raw41303step3Labels := by
      have ha : raw41303step3 = (fun i j => raw41303step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41303step3 raw41303step2; decide +kernel
      have hl : raw41303step3Labels = raw41303step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41303step2 raw41303step2Labels permutation4 permutation6
    mixedMoment B raw41303step3 raw41303step3Labels = mixedMoment B raw41303step4 raw41303step4Labels := by
      have ha : raw41303step4 = -raw41303step3 := by apply Matrix.ext; change ∀ i j, raw41303step4 i j = -(raw41303step3 i j); unfold raw41303step4 raw41303step3; decide +kernel
      have hl : raw41303step4Labels = raw41303step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw41304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw41304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41304step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw41304step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw41304step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw41304step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw41304step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw41304step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical41304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41304 raw41304Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw41304 raw41304Labels = mixedMoment B raw41304step0 raw41304step0Labels := by
      have hz : ∀ j, raw41304 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41304step0 = (fun i j => raw41304 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41304step0 raw41304; decide +kernel
      have hl : raw41304step0Labels = raw41304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41304 raw41304Labels permutation520 hz
    mixedMoment B raw41304step0 raw41304step0Labels = mixedMoment B raw41304step1 raw41304step1Labels := by
      have hz : ∀ j, raw41304step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41304step1 = (fun i j => raw41304step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41304step1 raw41304step0; decide +kernel
      have hl : raw41304step1Labels = raw41304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41304step0 raw41304step0Labels permutation104 hz
    mixedMoment B raw41304step1 raw41304step1Labels = mixedMoment B raw41304step2 raw41304step2Labels := by
      have hz : ∀ i, raw41304step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41304step2 = (fun i j => raw41304step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41304step2 raw41304step1; decide +kernel
      have hl : raw41304step2Labels = (fun j => raw41304step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41304step1 raw41304step1Labels permutation6 hz
    mixedMoment B raw41304step2 raw41304step2Labels = mixedMoment B raw41304step3 raw41304step3Labels := by
      have ha : raw41304step3 = (fun i j => raw41304step2 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw41304step3 raw41304step2; decide +kernel
      have hl : raw41304step3Labels = raw41304step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41304step2 raw41304step2Labels permutation26 permutation0
    mixedMoment B raw41304step3 raw41304step3Labels = mixedMoment B raw41304step4 raw41304step4Labels := by
      have ha : raw41304step4 = -raw41304step3 := by apply Matrix.ext; change ∀ i j, raw41304step4 i j = -(raw41304step3 i j); unfold raw41304step4 raw41304step3; decide +kernel
      have hl : raw41304step4Labels = raw41304step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw41305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw41305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -2, -1]]
def raw41305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41305step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41305 raw41305Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw41305 raw41305Labels = mixedMoment B raw41305step0 raw41305step0Labels := by
      have hz : ∀ j, raw41305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41305step0 = (fun i j => raw41305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41305step0 raw41305; decide +kernel
      have hl : raw41305step0Labels = raw41305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41305 raw41305Labels permutation434 hz
    mixedMoment B raw41305step0 raw41305step0Labels = mixedMoment B raw41305step1 raw41305step1Labels := by
      have ha : raw41305step1 = (fun i j => raw41305step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41305step1 raw41305step0; decide +kernel
      have hl : raw41305step1Labels = raw41305step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41305step0 raw41305step0Labels permutation146 permutation3
    mixedMoment B raw41305step1 raw41305step1Labels = mixedMoment B raw41305step2 raw41305step2Labels := by
      have ha : raw41305step2 = -raw41305step1 := by apply Matrix.ext; change ∀ i j, raw41305step2 i j = -(raw41305step1 i j); unfold raw41305step2 raw41305step1; decide +kernel
      have hl : raw41305step2Labels = raw41305step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2741 node2741Labels := by rfl

def raw41306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41306 raw41306Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw41306 raw41306Labels = mixedMoment B raw41306step0 raw41306step0Labels := by
      have hz : ∀ j, raw41306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41306step0 = (fun i j => raw41306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41306step0 raw41306; decide +kernel
      have hl : raw41306step0Labels = raw41306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41306 raw41306Labels permutation434 hz
    mixedMoment B raw41306step0 raw41306step0Labels = mixedMoment B raw41306step1 raw41306step1Labels := by
      have ha : raw41306step1 = (fun i j => raw41306step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41306step1 raw41306step0; decide +kernel
      have hl : raw41306step1Labels = raw41306step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41306step0 raw41306step0Labels permutation146 permutation3
    mixedMoment B raw41306step1 raw41306step1Labels = mixedMoment B raw41306step2 raw41306step2Labels := by
      have ha : raw41306step2 = -raw41306step1 := by apply Matrix.ext; change ∀ i j, raw41306step2 i j = -(raw41306step1 i j); unfold raw41306step2 raw41306step1; decide +kernel
      have hl : raw41306step2Labels = raw41306step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3962 node3962Labels := by rfl

def raw41307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw41307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw41307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41307 raw41307Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw41307 raw41307Labels = mixedMoment B raw41307step0 raw41307step0Labels := by
      have hz : ∀ j, raw41307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41307step0 = (fun i j => raw41307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41307step0 raw41307; decide +kernel
      have hl : raw41307step0Labels = raw41307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41307 raw41307Labels permutation434 hz
    mixedMoment B raw41307step0 raw41307step0Labels = mixedMoment B raw41307step1 raw41307step1Labels := by
      have ha : raw41307step1 = (fun i j => raw41307step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41307step1 raw41307step0; decide +kernel
      have hl : raw41307step1Labels = raw41307step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41307step0 raw41307step0Labels permutation104 permutation6
    mixedMoment B raw41307step1 raw41307step1Labels = mixedMoment B raw41307step2 raw41307step2Labels := by
      have ha : raw41307step2 = -raw41307step1 := by apply Matrix.ext; change ∀ i j, raw41307step2 i j = -(raw41307step1 i j); unfold raw41307step2 raw41307step1; decide +kernel
      have hl : raw41307step2Labels = raw41307step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw41308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41308 raw41308Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw41308 raw41308Labels = mixedMoment B raw41308step0 raw41308step0Labels := by
      have ha : raw41308step0 = (fun i j => raw41308 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41308step0 raw41308; decide +kernel
      have hl : raw41308step0Labels = raw41308Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41308 raw41308Labels permutation683 permutation3
    mixedMoment B raw41308step0 raw41308step0Labels = mixedMoment B raw41308step1 raw41308step1Labels := by
      have ha : raw41308step1 = -raw41308step0 := by apply Matrix.ext; change ∀ i j, raw41308step1 i j = -(raw41308step0 i j); unfold raw41308step1 raw41308step0; decide +kernel
      have hl : raw41308step1Labels = raw41308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw41309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41309 raw41309Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw41309 raw41309Labels = mixedMoment B raw41309step0 raw41309step0Labels := by
      have hz : ∀ j, raw41309 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41309step0 = (fun i j => raw41309 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41309step0 raw41309; decide +kernel
      have hl : raw41309step0Labels = raw41309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41309 raw41309Labels permutation520 hz
    mixedMoment B raw41309step0 raw41309step0Labels = mixedMoment B raw41309step1 raw41309step1Labels := by
      have ha : raw41309step1 = (fun i j => raw41309step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41309step1 raw41309step0; decide +kernel
      have hl : raw41309step1Labels = raw41309step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41309step0 raw41309step0Labels permutation150 permutation3
    mixedMoment B raw41309step1 raw41309step1Labels = mixedMoment B raw41309step2 raw41309step2Labels := by
      have ha : raw41309step2 = -raw41309step1 := by apply Matrix.ext; change ∀ i j, raw41309step2 i j = -(raw41309step1 i j); unfold raw41309step2 raw41309step1; decide +kernel
      have hl : raw41309step2Labels = raw41309step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw41310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw41310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41310 raw41310Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw41310 raw41310Labels = mixedMoment B raw41310step0 raw41310step0Labels := by
      have ha : raw41310step0 = (fun i j => raw41310 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41310step0 raw41310; decide +kernel
      have hl : raw41310step0Labels = raw41310Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41310 raw41310Labels permutation687 permutation3
    mixedMoment B raw41310step0 raw41310step0Labels = mixedMoment B raw41310step1 raw41310step1Labels := by
      have ha : raw41310step1 = -raw41310step0 := by apply Matrix.ext; change ∀ i j, raw41310step1 i j = -(raw41310step0 i j); unfold raw41310step1 raw41310step0; decide +kernel
      have hl : raw41310step1Labels = raw41310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw41311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41311 raw41311Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw41311 raw41311Labels = mixedMoment B raw41311step0 raw41311step0Labels := by
      have ha : raw41311step0 = (fun i j => raw41311 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41311step0 raw41311; decide +kernel
      have hl : raw41311step0Labels = raw41311Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41311 raw41311Labels permutation687 permutation3
    mixedMoment B raw41311step0 raw41311step0Labels = mixedMoment B raw41311step1 raw41311step1Labels := by
      have ha : raw41311step1 = -raw41311step0 := by apply Matrix.ext; change ∀ i j, raw41311step1 i j = -(raw41311step0 i j); unfold raw41311step1 raw41311step0; decide +kernel
      have hl : raw41311step1Labels = raw41311step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw41312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41312 raw41312Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw41312 raw41312Labels = mixedMoment B raw41312step0 raw41312step0Labels := by
      have ha : raw41312step0 = (fun i j => raw41312 (permutation541 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41312step0 raw41312; decide +kernel
      have hl : raw41312step0Labels = raw41312Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41312 raw41312Labels permutation541 permutation6
    mixedMoment B raw41312step0 raw41312step0Labels = mixedMoment B raw41312step1 raw41312step1Labels := by
      have ha : raw41312step1 = -raw41312step0 := by apply Matrix.ext; change ∀ i j, raw41312step1 i j = -(raw41312step0 i j); unfold raw41312step1 raw41312step0; decide +kernel
      have hl : raw41312step1Labels = raw41312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw41313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw41313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41313 raw41313Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw41313 raw41313Labels = mixedMoment B raw41313step0 raw41313step0Labels := by
      have hz : ∀ j, raw41313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41313step0 = (fun i j => raw41313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41313step0 raw41313; decide +kernel
      have hl : raw41313step0Labels = raw41313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41313 raw41313Labels permutation434 hz
    mixedMoment B raw41313step0 raw41313step0Labels = mixedMoment B raw41313step1 raw41313step1Labels := by
      have ha : raw41313step1 = (fun i j => raw41313step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41313step1 raw41313step0; decide +kernel
      have hl : raw41313step1Labels = raw41313step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41313step0 raw41313step0Labels permutation128 permutation6
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw41314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41314 raw41314Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw41314 raw41314Labels = mixedMoment B raw41314step0 raw41314step0Labels := by
      have ha : raw41314step0 = (fun i j => raw41314 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41314step0 raw41314; decide +kernel
      have hl : raw41314step0Labels = raw41314Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41314 raw41314Labels permutation590 permutation6
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw41315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw41315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw41315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41315 raw41315Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw41315 raw41315Labels = mixedMoment B raw41315step0 raw41315step0Labels := by
      have hz : ∀ j, raw41315 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41315step0 = (fun i j => raw41315 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41315step0 raw41315; decide +kernel
      have hl : raw41315step0Labels = raw41315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41315 raw41315Labels permutation520 hz
    mixedMoment B raw41315step0 raw41315step0Labels = mixedMoment B raw41315step1 raw41315step1Labels := by
      have ha : raw41315step1 = (fun i j => raw41315step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41315step1 raw41315step0; decide +kernel
      have hl : raw41315step1Labels = raw41315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41315step0 raw41315step0Labels permutation150 permutation3
    mixedMoment B raw41315step1 raw41315step1Labels = mixedMoment B raw41315step2 raw41315step2Labels := by
      have ha : raw41315step2 = -raw41315step1 := by apply Matrix.ext; change ∀ i j, raw41315step2 i j = -(raw41315step1 i j); unfold raw41315step2 raw41315step1; decide +kernel
      have hl : raw41315step2Labels = raw41315step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw41316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41316 raw41316Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw41316 raw41316Labels = mixedMoment B raw41316step0 raw41316step0Labels := by
      have ha : raw41316step0 = (fun i j => raw41316 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41316step0 raw41316; decide +kernel
      have hl : raw41316step0Labels = raw41316Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41316 raw41316Labels permutation399 permutation6
    mixedMoment B raw41316step0 raw41316step0Labels = mixedMoment B raw41316step1 raw41316step1Labels := by
      have ha : raw41316step1 = -raw41316step0 := by apply Matrix.ext; change ∀ i j, raw41316step1 i j = -(raw41316step0 i j); unfold raw41316step1 raw41316step0; decide +kernel
      have hl : raw41316step1Labels = raw41316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw41317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw41317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41317 raw41317Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw41317 raw41317Labels = mixedMoment B raw41317step0 raw41317step0Labels := by
      have hz : ∀ j, raw41317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41317step0 = (fun i j => raw41317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41317step0 raw41317; decide +kernel
      have hl : raw41317step0Labels = raw41317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41317 raw41317Labels permutation434 hz
    mixedMoment B raw41317step0 raw41317step0Labels = mixedMoment B raw41317step1 raw41317step1Labels := by
      have ha : raw41317step1 = (fun i j => raw41317step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41317step1 raw41317step0; decide +kernel
      have hl : raw41317step1Labels = raw41317step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41317step0 raw41317step0Labels permutation129 permutation6
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw41318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw41318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw41318step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3], ![2, 1, -3]]
def raw41318step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw41318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41318step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41318step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41318 raw41318Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw41318 raw41318Labels = mixedMoment B raw41318step0 raw41318step0Labels := by
      have hz : ∀ j, raw41318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41318step0 = (fun i j => raw41318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41318step0 raw41318; decide +kernel
      have hl : raw41318step0Labels = raw41318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41318 raw41318Labels permutation434 hz
    mixedMoment B raw41318step0 raw41318step0Labels = mixedMoment B raw41318step1 raw41318step1Labels := by
      have hz : ∀ j, raw41318step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41318step1 = (fun i j => raw41318step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41318step1 raw41318step0; decide +kernel
      have hl : raw41318step1Labels = raw41318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41318step0 raw41318step0Labels permutation80 hz
    mixedMoment B raw41318step1 raw41318step1Labels = mixedMoment B raw41318step2 raw41318step2Labels := by
      have ha : raw41318step2 = (fun i j => raw41318step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41318step2 raw41318step1; decide +kernel
      have hl : raw41318step2Labels = raw41318step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41318step1 raw41318step1Labels permutation20 permutation6
    mixedMoment B raw41318step2 raw41318step2Labels = mixedMoment B raw41318step3 raw41318step3Labels := by
      have ha : raw41318step3 = -raw41318step2 := by apply Matrix.ext; change ∀ i j, raw41318step3 i j = -(raw41318step2 i j); unfold raw41318step3 raw41318step2; decide +kernel
      have hl : raw41318step3Labels = raw41318step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw41319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw41319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw41319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -3, 2]]
def raw41319step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw41319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41319step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41319 raw41319Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw41319 raw41319Labels = mixedMoment B raw41319step0 raw41319step0Labels := by
      have hz : ∀ j, raw41319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41319step0 = (fun i j => raw41319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41319step0 raw41319; decide +kernel
      have hl : raw41319step0Labels = raw41319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41319 raw41319Labels permutation434 hz
    mixedMoment B raw41319step0 raw41319step0Labels = mixedMoment B raw41319step1 raw41319step1Labels := by
      have hz : ∀ j, raw41319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41319step1 = (fun i j => raw41319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41319step1 raw41319step0; decide +kernel
      have hl : raw41319step1Labels = raw41319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41319step0 raw41319step0Labels permutation80 hz
    mixedMoment B raw41319step1 raw41319step1Labels = mixedMoment B raw41319step2 raw41319step2Labels := by
      have ha : raw41319step2 = (fun i j => raw41319step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41319step2 raw41319step1; decide +kernel
      have hl : raw41319step2Labels = raw41319step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41319step1 raw41319step1Labels permutation26 permutation6
    mixedMoment B raw41319step2 raw41319step2Labels = mixedMoment B raw41319step3 raw41319step3Labels := by
      have ha : raw41319step3 = -raw41319step2 := by apply Matrix.ext; change ∀ i j, raw41319step3 i j = -(raw41319step2 i j); unfold raw41319step3 raw41319step2; decide +kernel
      have hl : raw41319step3Labels = raw41319step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

def raw41320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41320 raw41320Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw41320 raw41320Labels = mixedMoment B raw41320step0 raw41320step0Labels := by
      have hz : ∀ j, raw41320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41320step0 = (fun i j => raw41320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41320step0 raw41320; decide +kernel
      have hl : raw41320step0Labels = raw41320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41320 raw41320Labels permutation346 hz
    mixedMoment B raw41320step0 raw41320step0Labels = mixedMoment B raw41320step1 raw41320step1Labels := by
      have ha : raw41320step1 = (fun i j => raw41320step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41320step1 raw41320step0; decide +kernel
      have hl : raw41320step1Labels = raw41320step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41320step0 raw41320step0Labels permutation128 permutation6
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw41321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41321step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41321 raw41321Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw41321 raw41321Labels = mixedMoment B raw41321step0 raw41321step0Labels := by
      have hz : ∀ j, raw41321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41321step0 = (fun i j => raw41321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41321step0 raw41321; decide +kernel
      have hl : raw41321step0Labels = raw41321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41321 raw41321Labels permutation346 hz
    mixedMoment B raw41321step0 raw41321step0Labels = mixedMoment B raw41321step1 raw41321step1Labels := by
      have ha : raw41321step1 = (fun i j => raw41321step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41321step1 raw41321step0; decide +kernel
      have hl : raw41321step1Labels = raw41321step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41321step0 raw41321step0Labels permutation104 permutation6
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw41322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw41322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw41322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41322step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41322 raw41322Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw41322 raw41322Labels = mixedMoment B raw41322step0 raw41322step0Labels := by
      have hz : ∀ j, raw41322 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41322step0 = (fun i j => raw41322 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41322step0 raw41322; decide +kernel
      have hl : raw41322step0Labels = raw41322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41322 raw41322Labels permutation520 hz
    mixedMoment B raw41322step0 raw41322step0Labels = mixedMoment B raw41322step1 raw41322step1Labels := by
      have ha : raw41322step1 = (fun i j => raw41322step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41322step1 raw41322step0; decide +kernel
      have hl : raw41322step1Labels = raw41322step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41322step0 raw41322step0Labels permutation149 permutation3
    mixedMoment B raw41322step1 raw41322step1Labels = mixedMoment B raw41322step2 raw41322step2Labels := by
      have ha : raw41322step2 = -raw41322step1 := by apply Matrix.ext; change ∀ i j, raw41322step2 i j = -(raw41322step1 i j); unfold raw41322step2 raw41322step1; decide +kernel
      have hl : raw41322step2Labels = raw41322step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw41323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw41323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41323 raw41323Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw41323 raw41323Labels = mixedMoment B raw41323step0 raw41323step0Labels := by
      have ha : raw41323step0 = (fun i j => raw41323 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41323step0 raw41323; decide +kernel
      have hl : raw41323step0Labels = raw41323Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41323 raw41323Labels permutation686 permutation3
    mixedMoment B raw41323step0 raw41323step0Labels = mixedMoment B raw41323step1 raw41323step1Labels := by
      have ha : raw41323step1 = -raw41323step0 := by apply Matrix.ext; change ∀ i j, raw41323step1 i j = -(raw41323step0 i j); unfold raw41323step1 raw41323step0; decide +kernel
      have hl : raw41323step1Labels = raw41323step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw41324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![3, -1, -2]]
def raw41324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41324 raw41324Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw41324 raw41324Labels = mixedMoment B raw41324step0 raw41324step0Labels := by
      have ha : raw41324step0 = (fun i j => raw41324 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41324step0 raw41324; decide +kernel
      have hl : raw41324step0Labels = raw41324Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41324 raw41324Labels permutation686 permutation3
    mixedMoment B raw41324step0 raw41324step0Labels = mixedMoment B raw41324step1 raw41324step1Labels := by
      have ha : raw41324step1 = -raw41324step0 := by apply Matrix.ext; change ∀ i j, raw41324step1 i j = -(raw41324step0 i j); unfold raw41324step1 raw41324step0; decide +kernel
      have hl : raw41324step1Labels = raw41324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3043 node3043Labels := by rfl

def raw41325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw41325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41325 raw41325Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw41325 raw41325Labels = mixedMoment B raw41325step0 raw41325step0Labels := by
      have ha : raw41325step0 = (fun i j => raw41325 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41325step0 raw41325; decide +kernel
      have hl : raw41325step0Labels = raw41325Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41325 raw41325Labels permutation686 permutation3
    mixedMoment B raw41325step0 raw41325step0Labels = mixedMoment B raw41325step1 raw41325step1Labels := by
      have ha : raw41325step1 = -raw41325step0 := by apply Matrix.ext; change ∀ i j, raw41325step1 i j = -(raw41325step0 i j); unfold raw41325step1 raw41325step0; decide +kernel
      have hl : raw41325step1Labels = raw41325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw41326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw41326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41326 raw41326Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw41326 raw41326Labels = mixedMoment B raw41326step0 raw41326step0Labels := by
      have ha : raw41326step0 = (fun i j => raw41326 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41326step0 raw41326; decide +kernel
      have hl : raw41326step0Labels = raw41326Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41326 raw41326Labels permutation505 permutation6
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw41327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw41327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41327 raw41327Labels = mixedMoment B node3488 node3488Labels := by
  calc
    mixedMoment B raw41327 raw41327Labels = mixedMoment B raw41327step0 raw41327step0Labels := by
      have ha : raw41327step0 = (fun i j => raw41327 (permutation531 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41327step0 raw41327; decide +kernel
      have hl : raw41327step0Labels = raw41327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41327 raw41327Labels permutation531 permutation6
    mixedMoment B raw41327step0 raw41327step0Labels = mixedMoment B raw41327step1 raw41327step1Labels := by
      have ha : raw41327step1 = -raw41327step0 := by apply Matrix.ext; change ∀ i j, raw41327step1 i j = -(raw41327step0 i j); unfold raw41327step1 raw41327step0; decide +kernel
      have hl : raw41327step1Labels = raw41327step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3488 node3488Labels := by rfl

def raw41328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41328 raw41328Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw41328 raw41328Labels = mixedMoment B raw41328step0 raw41328step0Labels := by
      have ha : raw41328step0 = (fun i j => raw41328 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41328step0 raw41328; decide +kernel
      have hl : raw41328step0Labels = raw41328Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41328 raw41328Labels permutation662 permutation3
    mixedMoment B raw41328step0 raw41328step0Labels = mixedMoment B raw41328step1 raw41328step1Labels := by
      have ha : raw41328step1 = -raw41328step0 := by apply Matrix.ext; change ∀ i j, raw41328step1 i j = -(raw41328step0 i j); unfold raw41328step1 raw41328step0; decide +kernel
      have hl : raw41328step1Labels = raw41328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw41329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw41329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41329 raw41329Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw41329 raw41329Labels = mixedMoment B raw41329step0 raw41329step0Labels := by
      have ha : raw41329step0 = (fun i j => raw41329 (permutation647 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41329step0 raw41329; decide +kernel
      have hl : raw41329step0Labels = raw41329Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41329 raw41329Labels permutation647 permutation6
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw41330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw41330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw41330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41330 raw41330Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw41330 raw41330Labels = mixedMoment B raw41330step0 raw41330step0Labels := by
      have hz : ∀ j, raw41330 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41330step0 = (fun i j => raw41330 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41330step0 raw41330; decide +kernel
      have hl : raw41330step0Labels = raw41330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41330 raw41330Labels permutation434 hz
    mixedMoment B raw41330step0 raw41330step0Labels = mixedMoment B raw41330step1 raw41330step1Labels := by
      have ha : raw41330step1 = (fun i j => raw41330step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41330step1 raw41330step0; decide +kernel
      have hl : raw41330step1Labels = raw41330step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41330step0 raw41330step0Labels permutation128 permutation6
    _ = mixedMoment B node1234 node1234Labels := by rfl

def raw41331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw41331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41331 raw41331Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw41331 raw41331Labels = mixedMoment B raw41331step0 raw41331step0Labels := by
      have ha : raw41331step0 = (fun i j => raw41331 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41331step0 raw41331; decide +kernel
      have hl : raw41331step0Labels = raw41331Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41331 raw41331Labels permutation590 permutation6
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw41332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw41332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41332 raw41332Labels = mixedMoment B node1212 node1212Labels := by
  calc
    mixedMoment B raw41332 raw41332Labels = mixedMoment B raw41332step0 raw41332step0Labels := by
      have ha : raw41332step0 = (fun i j => raw41332 (permutation599 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41332step0 raw41332; decide +kernel
      have hl : raw41332step0Labels = raw41332Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41332 raw41332Labels permutation599 permutation6
    _ = mixedMoment B node1212 node1212Labels := by rfl

def raw41333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw41333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![3, -2, -1]]
def raw41333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw41333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41333 raw41333Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw41333 raw41333Labels = mixedMoment B raw41333step0 raw41333step0Labels := by
      have hz : ∀ j, raw41333 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41333step0 = (fun i j => raw41333 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41333step0 raw41333; decide +kernel
      have hl : raw41333step0Labels = raw41333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41333 raw41333Labels permutation520 hz
    mixedMoment B raw41333step0 raw41333step0Labels = mixedMoment B raw41333step1 raw41333step1Labels := by
      have ha : raw41333step1 = (fun i j => raw41333step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41333step1 raw41333step0; decide +kernel
      have hl : raw41333step1Labels = raw41333step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41333step0 raw41333step0Labels permutation151 permutation3
    mixedMoment B raw41333step1 raw41333step1Labels = mixedMoment B raw41333step2 raw41333step2Labels := by
      have ha : raw41333step2 = -raw41333step1 := by apply Matrix.ext; change ∀ i j, raw41333step2 i j = -(raw41333step1 i j); unfold raw41333step2 raw41333step1; decide +kernel
      have hl : raw41333step2Labels = raw41333step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw41334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41334 raw41334Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw41334 raw41334Labels = mixedMoment B raw41334step0 raw41334step0Labels := by
      have ha : raw41334step0 = (fun i j => raw41334 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41334step0 raw41334; decide +kernel
      have hl : raw41334step0Labels = raw41334Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41334 raw41334Labels permutation506 permutation6
    _ = mixedMoment B node3720 node3720Labels := by rfl

def raw41335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw41335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41335 raw41335Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw41335 raw41335Labels = mixedMoment B raw41335step0 raw41335step0Labels := by
      have ha : raw41335step0 = (fun i j => raw41335 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41335step0 raw41335; decide +kernel
      have hl : raw41335step0Labels = raw41335Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41335 raw41335Labels permutation664 permutation3
    mixedMoment B raw41335step0 raw41335step0Labels = mixedMoment B raw41335step1 raw41335step1Labels := by
      have ha : raw41335step1 = -raw41335step0 := by apply Matrix.ext; change ∀ i j, raw41335step1 i j = -(raw41335step0 i j); unfold raw41335step1 raw41335step0; decide +kernel
      have hl : raw41335step1Labels = raw41335step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw41336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41336 raw41336Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw41336 raw41336Labels = mixedMoment B raw41336step0 raw41336step0Labels := by
      have ha : raw41336step0 = (fun i j => raw41336 (permutation648 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41336step0 raw41336; decide +kernel
      have hl : raw41336step0Labels = raw41336Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41336 raw41336Labels permutation648 permutation6
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw41337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw41337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41337 raw41337Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw41337 raw41337Labels = mixedMoment B raw41337step0 raw41337step0Labels := by
      have hz : ∀ j, raw41337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41337step0 = (fun i j => raw41337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41337step0 raw41337; decide +kernel
      have hl : raw41337step0Labels = raw41337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41337 raw41337Labels permutation434 hz
    mixedMoment B raw41337step0 raw41337step0Labels = mixedMoment B raw41337step1 raw41337step1Labels := by
      have ha : raw41337step1 = (fun i j => raw41337step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41337step1 raw41337step0; decide +kernel
      have hl : raw41337step1Labels = raw41337step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41337step0 raw41337step0Labels permutation129 permutation6
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw41338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![3, -1, -2]]
def raw41338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![3, -1, -2]]
def raw41338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41338 raw41338Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw41338 raw41338Labels = mixedMoment B raw41338step0 raw41338step0Labels := by
      have hz : ∀ j, raw41338 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41338step0 = (fun i j => raw41338 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41338step0 raw41338; decide +kernel
      have hl : raw41338step0Labels = raw41338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41338 raw41338Labels permutation520 hz
    mixedMoment B raw41338step0 raw41338step0Labels = mixedMoment B raw41338step1 raw41338step1Labels := by
      have ha : raw41338step1 = (fun i j => raw41338step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41338step1 raw41338step0; decide +kernel
      have hl : raw41338step1Labels = raw41338step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41338step0 raw41338step0Labels permutation87 permutation6
    mixedMoment B raw41338step1 raw41338step1Labels = mixedMoment B raw41338step2 raw41338step2Labels := by
      have ha : raw41338step2 = -raw41338step1 := by apply Matrix.ext; change ∀ i j, raw41338step2 i j = -(raw41338step1 i j); unfold raw41338step2 raw41338step1; decide +kernel
      have hl : raw41338step2Labels = raw41338step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw41339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41339 raw41339Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw41339 raw41339Labels = mixedMoment B raw41339step0 raw41339step0Labels := by
      have ha : raw41339step0 = (fun i j => raw41339 (permutation376 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41339step0 raw41339; decide +kernel
      have hl : raw41339step0Labels = raw41339Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41339 raw41339Labels permutation376 permutation6
    mixedMoment B raw41339step0 raw41339step0Labels = mixedMoment B raw41339step1 raw41339step1Labels := by
      have ha : raw41339step1 = -raw41339step0 := by apply Matrix.ext; change ∀ i j, raw41339step1 i j = -(raw41339step0 i j); unfold raw41339step1 raw41339step0; decide +kernel
      have hl : raw41339step1Labels = raw41339step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw41340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw41340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41340 raw41340Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw41340 raw41340Labels = mixedMoment B raw41340step0 raw41340step0Labels := by
      have hz : ∀ j, raw41340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41340step0 = (fun i j => raw41340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41340step0 raw41340; decide +kernel
      have hl : raw41340step0Labels = raw41340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41340 raw41340Labels permutation434 hz
    mixedMoment B raw41340step0 raw41340step0Labels = mixedMoment B raw41340step1 raw41340step1Labels := by
      have ha : raw41340step1 = (fun i j => raw41340step0 (permutation132 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41340step1 raw41340step0; decide +kernel
      have hl : raw41340step1Labels = raw41340step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41340step0 raw41340step0Labels permutation132 permutation6
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw41341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw41341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0]]
def raw41341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw41341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw41341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41341 raw41341Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw41341 raw41341Labels = mixedMoment B raw41341step0 raw41341step0Labels := by
      have hz : ∀ j, raw41341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41341step0 = (fun i j => raw41341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41341step0 raw41341; decide +kernel
      have hl : raw41341step0Labels = raw41341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41341 raw41341Labels permutation434 hz
    mixedMoment B raw41341step0 raw41341step0Labels = mixedMoment B raw41341step1 raw41341step1Labels := by
      have ha : raw41341step1 = (fun i j => raw41341step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41341step1 raw41341step0; decide +kernel
      have hl : raw41341step1Labels = raw41341step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41341step0 raw41341step0Labels permutation151 permutation3
    mixedMoment B raw41341step1 raw41341step1Labels = mixedMoment B raw41341step2 raw41341step2Labels := by
      have ha : raw41341step2 = -raw41341step1 := by apply Matrix.ext; change ∀ i j, raw41341step2 i j = -(raw41341step1 i j); unfold raw41341step2 raw41341step1; decide +kernel
      have hl : raw41341step2Labels = raw41341step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw41342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw41342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![2, -1, -1]]
def raw41342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw41342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41342 raw41342Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw41342 raw41342Labels = mixedMoment B raw41342step0 raw41342step0Labels := by
      have hz : ∀ j, raw41342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41342step0 = (fun i j => raw41342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41342step0 raw41342; decide +kernel
      have hl : raw41342step0Labels = raw41342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41342 raw41342Labels permutation434 hz
    mixedMoment B raw41342step0 raw41342step0Labels = mixedMoment B raw41342step1 raw41342step1Labels := by
      have ha : raw41342step1 = (fun i j => raw41342step0 (permutation111 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41342step1 raw41342step0; decide +kernel
      have hl : raw41342step1Labels = raw41342step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41342step0 raw41342step0Labels permutation111 permutation6
    mixedMoment B raw41342step1 raw41342step1Labels = mixedMoment B raw41342step2 raw41342step2Labels := by
      have ha : raw41342step2 = -raw41342step1 := by apply Matrix.ext; change ∀ i j, raw41342step2 i j = -(raw41342step1 i j); unfold raw41342step2 raw41342step1; decide +kernel
      have hl : raw41342step2Labels = raw41342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw41343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw41343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -3, 3], ![2, 0, -2]]
def raw41343step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41343 raw41343Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw41343 raw41343Labels = mixedMoment B raw41343step0 raw41343step0Labels := by
      have hz : ∀ j, raw41343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41343step0 = (fun i j => raw41343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41343step0 raw41343; decide +kernel
      have hl : raw41343step0Labels = raw41343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41343 raw41343Labels permutation434 hz
    mixedMoment B raw41343step0 raw41343step0Labels = mixedMoment B raw41343step1 raw41343step1Labels := by
      have ha : raw41343step1 = (fun i j => raw41343step0 (permutation111 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41343step1 raw41343step0; decide +kernel
      have hl : raw41343step1Labels = raw41343step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41343step0 raw41343step0Labels permutation111 permutation6
    mixedMoment B raw41343step1 raw41343step1Labels = mixedMoment B raw41343step2 raw41343step2Labels := by
      have ha : raw41343step2 = -raw41343step1 := by apply Matrix.ext; change ∀ i j, raw41343step2 i j = -(raw41343step1 i j); unfold raw41343step2 raw41343step1; decide +kernel
      have hl : raw41343step2Labels = raw41343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
