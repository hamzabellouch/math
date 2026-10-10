import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15744 raw15744Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw15744 raw15744Labels = mixedMoment B raw15744step0 raw15744step0Labels := by
      have hz : ∀ j, raw15744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15744step0 = (fun i j => raw15744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15744step0 raw15744; decide +kernel
      have hl : raw15744step0Labels = raw15744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15744 raw15744Labels permutation346 hz
    mixedMoment B raw15744step0 raw15744step0Labels = mixedMoment B raw15744step1 raw15744step1Labels := by
      have ha : raw15744step1 = (fun i j => raw15744step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15744step1 raw15744step0; decide +kernel
      have hl : raw15744step1Labels = raw15744step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15744step0 raw15744step0Labels permutation44 permutation4
    mixedMoment B raw15744step1 raw15744step1Labels = mixedMoment B raw15744step2 raw15744step2Labels := by
      have ha : raw15744step2 = -raw15744step1 := by apply Matrix.ext; change ∀ i j, raw15744step2 i j = -(raw15744step1 i j); unfold raw15744step2 raw15744step1; decide +kernel
      have hl : raw15744step2Labels = raw15744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw15745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15745 raw15745Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw15745 raw15745Labels = mixedMoment B raw15745step0 raw15745step0Labels := by
      have hz : ∀ j, raw15745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15745step0 = (fun i j => raw15745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15745step0 raw15745; decide +kernel
      have hl : raw15745step0Labels = raw15745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15745 raw15745Labels permutation434 hz
    mixedMoment B raw15745step0 raw15745step0Labels = mixedMoment B raw15745step1 raw15745step1Labels := by
      have ha : raw15745step1 = (fun i j => raw15745step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15745step1 raw15745step0; decide +kernel
      have hl : raw15745step1Labels = raw15745step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15745step0 raw15745step0Labels permutation44 permutation4
    mixedMoment B raw15745step1 raw15745step1Labels = mixedMoment B raw15745step2 raw15745step2Labels := by
      have ha : raw15745step2 = -raw15745step1 := by apply Matrix.ext; change ∀ i j, raw15745step2 i j = -(raw15745step1 i j); unfold raw15745step2 raw15745step1; decide +kernel
      have hl : raw15745step2Labels = raw15745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw15746 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15746 raw15746Labels = mixedMoment B node2869 node2869Labels := by
  calc
    mixedMoment B raw15746 raw15746Labels = mixedMoment B raw15746step0 raw15746step0Labels := by
      have ha : raw15746step0 = (fun i j => raw15746 (permutation572 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15746step0 raw15746; decide +kernel
      have hl : raw15746step0Labels = raw15746Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15746 raw15746Labels permutation572 permutation2
    _ = mixedMoment B node2869 node2869Labels := by rfl

def raw15747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15747 raw15747Labels = mixedMoment B node3697 node3697Labels := by
  calc
    mixedMoment B raw15747 raw15747Labels = mixedMoment B raw15747step0 raw15747step0Labels := by
      have ha : raw15747step0 = (fun i j => raw15747 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15747step0 raw15747; decide +kernel
      have hl : raw15747step0Labels = raw15747Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15747 raw15747Labels permutation668 permutation2
    _ = mixedMoment B node3697 node3697Labels := by rfl

def raw15748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15748 raw15748Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw15748 raw15748Labels = mixedMoment B raw15748step0 raw15748step0Labels := by
      have ha : raw15748step0 = (fun i j => raw15748 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15748step0 raw15748; decide +kernel
      have hl : raw15748step0Labels = raw15748Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15748 raw15748Labels permutation167 permutation4
    mixedMoment B raw15748step0 raw15748step0Labels = mixedMoment B raw15748step1 raw15748step1Labels := by
      have ha : raw15748step1 = -raw15748step0 := by apply Matrix.ext; change ∀ i j, raw15748step1 i j = -(raw15748step0 i j); unfold raw15748step1 raw15748step0; decide +kernel
      have hl : raw15748step1Labels = raw15748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw15749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15749 raw15749Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw15749 raw15749Labels = mixedMoment B raw15749step0 raw15749step0Labels := by
      have ha : raw15749step0 = (fun i j => raw15749 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15749step0 raw15749; decide +kernel
      have hl : raw15749step0Labels = raw15749Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15749 raw15749Labels permutation165 permutation4
    mixedMoment B raw15749step0 raw15749step0Labels = mixedMoment B raw15749step1 raw15749step1Labels := by
      have ha : raw15749step1 = -raw15749step0 := by apply Matrix.ext; change ∀ i j, raw15749step1 i j = -(raw15749step0 i j); unfold raw15749step1 raw15749step0; decide +kernel
      have hl : raw15749step1Labels = raw15749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw15750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15750 raw15750Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw15750 raw15750Labels = mixedMoment B raw15750step0 raw15750step0Labels := by
      have ha : raw15750step0 = (fun i j => raw15750 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15750step0 raw15750; decide +kernel
      have hl : raw15750step0Labels = raw15750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15750 raw15750Labels permutation164 permutation4
    mixedMoment B raw15750step0 raw15750step0Labels = mixedMoment B raw15750step1 raw15750step1Labels := by
      have ha : raw15750step1 = -raw15750step0 := by apply Matrix.ext; change ∀ i j, raw15750step1 i j = -(raw15750step0 i j); unfold raw15750step1 raw15750step0; decide +kernel
      have hl : raw15750step1Labels = raw15750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw15751 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15751 raw15751Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw15751 raw15751Labels = mixedMoment B raw15751step0 raw15751step0Labels := by
      have ha : raw15751step0 = (fun i j => raw15751 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15751step0 raw15751; decide +kernel
      have hl : raw15751step0Labels = raw15751Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15751 raw15751Labels permutation164 permutation4
    mixedMoment B raw15751step0 raw15751step0Labels = mixedMoment B raw15751step1 raw15751step1Labels := by
      have ha : raw15751step1 = -raw15751step0 := by apply Matrix.ext; change ∀ i j, raw15751step1 i j = -(raw15751step0 i j); unfold raw15751step1 raw15751step0; decide +kernel
      have hl : raw15751step1Labels = raw15751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3786 node3786Labels := by rfl

def raw15752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15752 raw15752Labels = mixedMoment B node2870 node2870Labels := by
  calc
    mixedMoment B raw15752 raw15752Labels = mixedMoment B raw15752step0 raw15752step0Labels := by
      have ha : raw15752step0 = (fun i j => raw15752 (permutation573 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15752step0 raw15752; decide +kernel
      have hl : raw15752step0Labels = raw15752Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15752 raw15752Labels permutation573 permutation2
    _ = mixedMoment B node2870 node2870Labels := by rfl

def raw15753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15753 raw15753Labels = mixedMoment B node2870 node2870Labels := by
  calc
    mixedMoment B raw15753 raw15753Labels = mixedMoment B raw15753step0 raw15753step0Labels := by
      have ha : raw15753step0 = (fun i j => raw15753 (permutation571 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15753step0 raw15753; decide +kernel
      have hl : raw15753step0Labels = raw15753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15753 raw15753Labels permutation571 permutation2
    _ = mixedMoment B node2870 node2870Labels := by rfl

def raw15754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw15754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15754 raw15754Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw15754 raw15754Labels = mixedMoment B raw15754step0 raw15754step0Labels := by
      have ha : raw15754step0 = (fun i j => raw15754 (permutation572 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15754step0 raw15754; decide +kernel
      have hl : raw15754step0Labels = raw15754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15754 raw15754Labels permutation572 permutation2
    _ = mixedMoment B node3043 node3043Labels := by rfl

def raw15755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15755 raw15755Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw15755 raw15755Labels = mixedMoment B raw15755step0 raw15755step0Labels := by
      have ha : raw15755step0 = (fun i j => raw15755 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15755step0 raw15755; decide +kernel
      have hl : raw15755step0Labels = raw15755Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15755 raw15755Labels permutation224 permutation4
    mixedMoment B raw15755step0 raw15755step0Labels = mixedMoment B raw15755step1 raw15755step1Labels := by
      have ha : raw15755step1 = -raw15755step0 := by apply Matrix.ext; change ∀ i j, raw15755step1 i j = -(raw15755step0 i j); unfold raw15755step1 raw15755step0; decide +kernel
      have hl : raw15755step1Labels = raw15755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2614 node2614Labels := by rfl

def raw15756 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15756 raw15756Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15756 raw15756Labels = mixedMoment B raw15756step0 raw15756step0Labels := by
      have hz : ∀ j, raw15756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15756step0 = (fun i j => raw15756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15756step0 raw15756; decide +kernel
      have hl : raw15756step0Labels = raw15756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15756 raw15756Labels permutation346 hz
    mixedMoment B raw15756step0 raw15756step0Labels = mixedMoment B raw15756step1 raw15756step1Labels := by
      have ha : raw15756step1 = (fun i j => raw15756step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15756step1 raw15756step0; decide +kernel
      have hl : raw15756step1Labels = raw15756step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15756step0 raw15756step0Labels permutation143 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw15757 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15757 raw15757Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15757 raw15757Labels = mixedMoment B raw15757step0 raw15757step0Labels := by
      have hz : ∀ j, raw15757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15757step0 = (fun i j => raw15757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15757step0 raw15757; decide +kernel
      have hl : raw15757step0Labels = raw15757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15757 raw15757Labels permutation434 hz
    mixedMoment B raw15757step0 raw15757step0Labels = mixedMoment B raw15757step1 raw15757step1Labels := by
      have ha : raw15757step1 = (fun i j => raw15757step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15757step1 raw15757step0; decide +kernel
      have hl : raw15757step1Labels = raw15757step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15757step0 raw15757step0Labels permutation143 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw15758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15758step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15758 raw15758Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw15758 raw15758Labels = mixedMoment B raw15758step0 raw15758step0Labels := by
      have ha : raw15758step0 = (fun i j => raw15758 (permutation668 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15758step0 raw15758; decide +kernel
      have hl : raw15758step0Labels = raw15758Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15758 raw15758Labels permutation668 permutation5
    mixedMoment B raw15758step0 raw15758step0Labels = mixedMoment B raw15758step1 raw15758step1Labels := by
      have ha : raw15758step1 = raw15758step0 := by apply Matrix.ext; unfold raw15758step1 raw15758step0; decide +kernel
      have hl : raw15758step0Labels = labelEmbedding8 ∘ raw15758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15758step0 raw15758step0Labels raw15758step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw15759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15759step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15759 raw15759Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw15759 raw15759Labels = mixedMoment B raw15759step0 raw15759step0Labels := by
      have ha : raw15759step0 = (fun i j => raw15759 (permutation669 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15759step0 raw15759; decide +kernel
      have hl : raw15759step0Labels = raw15759Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15759 raw15759Labels permutation669 permutation5
    mixedMoment B raw15759step0 raw15759step0Labels = mixedMoment B raw15759step1 raw15759step1Labels := by
      have ha : raw15759step1 = raw15759step0 := by apply Matrix.ext; unfold raw15759step1 raw15759step0; decide +kernel
      have hl : raw15759step0Labels = labelEmbedding8 ∘ raw15759step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15759step0 raw15759step0Labels raw15759step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw15760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15760step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15760 raw15760Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw15760 raw15760Labels = mixedMoment B raw15760step0 raw15760step0Labels := by
      have ha : raw15760step0 = (fun i j => raw15760 (permutation667 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15760step0 raw15760; decide +kernel
      have hl : raw15760step0Labels = raw15760Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15760 raw15760Labels permutation667 permutation5
    mixedMoment B raw15760step0 raw15760step0Labels = mixedMoment B raw15760step1 raw15760step1Labels := by
      have ha : raw15760step1 = raw15760step0 := by apply Matrix.ext; unfold raw15760step1 raw15760step0; decide +kernel
      have hl : raw15760step0Labels = labelEmbedding8 ∘ raw15760step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15760step0 raw15760step0Labels raw15760step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw15761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw15761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw15761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15761step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15761step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15761 raw15761Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw15761 raw15761Labels = mixedMoment B raw15761step0 raw15761step0Labels := by
      have hz : ∀ j, raw15761 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15761step0 = (fun i j => raw15761 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15761step0 raw15761; decide +kernel
      have hl : raw15761step0Labels = raw15761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15761 raw15761Labels permutation520 hz
    mixedMoment B raw15761step0 raw15761step0Labels = mixedMoment B raw15761step1 raw15761step1Labels := by
      have ha : raw15761step1 = (fun i j => raw15761step0 (permutation131 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15761step1 raw15761step0; decide +kernel
      have hl : raw15761step1Labels = raw15761step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15761step0 raw15761step0Labels permutation131 permutation5
    mixedMoment B raw15761step1 raw15761step1Labels = mixedMoment B raw15761step2 raw15761step2Labels := by
      have ha : raw15761step2 = raw15761step1 := by apply Matrix.ext; unfold raw15761step2 raw15761step1; decide +kernel
      have hl : raw15761step1Labels = labelEmbedding8 ∘ raw15761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15761step1 raw15761step1Labels raw15761step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw15762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15762step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15762 raw15762Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw15762 raw15762Labels = mixedMoment B raw15762step0 raw15762step0Labels := by
      have ha : raw15762step0 = (fun i j => raw15762 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15762step0 raw15762; decide +kernel
      have hl : raw15762step0Labels = raw15762Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15762 raw15762Labels permutation271 permutation3
    mixedMoment B raw15762step0 raw15762step0Labels = mixedMoment B raw15762step1 raw15762step1Labels := by
      have ha : raw15762step1 = raw15762step0 := by apply Matrix.ext; unfold raw15762step1 raw15762step0; decide +kernel
      have hl : raw15762step0Labels = labelEmbedding6 ∘ raw15762step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15762step0 raw15762step0Labels raw15762step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw15763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15763 raw15763Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw15763 raw15763Labels = mixedMoment B raw15763step0 raw15763step0Labels := by
      have ha : raw15763step0 = (fun i j => raw15763 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15763step0 raw15763; decide +kernel
      have hl : raw15763step0Labels = raw15763Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15763 raw15763Labels permutation680 permutation3
    mixedMoment B raw15763step0 raw15763step0Labels = mixedMoment B raw15763step1 raw15763step1Labels := by
      have ha : raw15763step1 = -raw15763step0 := by apply Matrix.ext; change ∀ i j, raw15763step1 i j = -(raw15763step0 i j); unfold raw15763step1 raw15763step0; decide +kernel
      have hl : raw15763step1Labels = raw15763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15763step1 raw15763step1Labels = mixedMoment B raw15763step2 raw15763step2Labels := by
      have ha : raw15763step2 = raw15763step1 := by apply Matrix.ext; unfold raw15763step2 raw15763step1; decide +kernel
      have hl : raw15763step1Labels = labelEmbedding6 ∘ raw15763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15763step1 raw15763step1Labels raw15763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw15764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw15764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw15764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15764 raw15764Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw15764 raw15764Labels = mixedMoment B raw15764step0 raw15764step0Labels := by
      have hz : ∀ j, raw15764 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15764step0 = (fun i j => raw15764 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15764step0 raw15764; decide +kernel
      have hl : raw15764step0Labels = raw15764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15764 raw15764Labels permutation520 hz
    mixedMoment B raw15764step0 raw15764step0Labels = mixedMoment B raw15764step1 raw15764step1Labels := by
      have ha : raw15764step1 = (fun i j => raw15764step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15764step1 raw15764step0; decide +kernel
      have hl : raw15764step1Labels = raw15764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15764step0 raw15764step0Labels permutation34 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw15765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15765step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15765 raw15765Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw15765 raw15765Labels = mixedMoment B raw15765step0 raw15765step0Labels := by
      have ha : raw15765step0 = (fun i j => raw15765 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15765step0 raw15765; decide +kernel
      have hl : raw15765step0Labels = raw15765Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15765 raw15765Labels permutation265 permutation3
    mixedMoment B raw15765step0 raw15765step0Labels = mixedMoment B raw15765step1 raw15765step1Labels := by
      have ha : raw15765step1 = raw15765step0 := by apply Matrix.ext; unfold raw15765step1 raw15765step0; decide +kernel
      have hl : raw15765step0Labels = labelEmbedding6 ∘ raw15765step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15765step0 raw15765step0Labels raw15765step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw15766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15766step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15766 raw15766Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw15766 raw15766Labels = mixedMoment B raw15766step0 raw15766step0Labels := by
      have ha : raw15766step0 = (fun i j => raw15766 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15766step0 raw15766; decide +kernel
      have hl : raw15766step0Labels = raw15766Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15766 raw15766Labels permutation686 permutation3
    mixedMoment B raw15766step0 raw15766step0Labels = mixedMoment B raw15766step1 raw15766step1Labels := by
      have ha : raw15766step1 = -raw15766step0 := by apply Matrix.ext; change ∀ i j, raw15766step1 i j = -(raw15766step0 i j); unfold raw15766step1 raw15766step0; decide +kernel
      have hl : raw15766step1Labels = raw15766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15766step1 raw15766step1Labels = mixedMoment B raw15766step2 raw15766step2Labels := by
      have ha : raw15766step2 = raw15766step1 := by apply Matrix.ext; unfold raw15766step2 raw15766step1; decide +kernel
      have hl : raw15766step1Labels = labelEmbedding6 ∘ raw15766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15766step1 raw15766step1Labels raw15766step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw15767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw15767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15767 raw15767Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw15767 raw15767Labels = mixedMoment B raw15767step0 raw15767step0Labels := by
      have hz : ∀ j, raw15767 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15767step0 = (fun i j => raw15767 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15767step0 raw15767; decide +kernel
      have hl : raw15767step0Labels = raw15767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15767 raw15767Labels permutation520 hz
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw15768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw15768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15768step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15768step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15768step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15768 raw15768Labels = mixedMoment B node5320 node5320Labels := by
  calc
    mixedMoment B raw15768 raw15768Labels = mixedMoment B raw15768step0 raw15768step0Labels := by
      have ha : raw15768step0 = (fun i j => raw15768 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15768step0 raw15768; decide +kernel
      have hl : raw15768step0Labels = raw15768Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15768 raw15768Labels permutation583 permutation3
    mixedMoment B raw15768step0 raw15768step0Labels = mixedMoment B raw15768step1 raw15768step1Labels := by
      have ha : raw15768step1 = -raw15768step0 := by apply Matrix.ext; change ∀ i j, raw15768step1 i j = -(raw15768step0 i j); unfold raw15768step1 raw15768step0; decide +kernel
      have hl : raw15768step1Labels = raw15768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15768step1 raw15768step1Labels = mixedMoment B raw15768step2 raw15768step2Labels := by
      have ha : raw15768step2 = raw15768step1 := by apply Matrix.ext; unfold raw15768step2 raw15768step1; decide +kernel
      have hl : raw15768step1Labels = labelEmbedding6 ∘ raw15768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15768step1 raw15768step1Labels raw15768step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5320 node5320Labels := by rfl

def raw15769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw15769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15769step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15769 raw15769Labels = mixedMoment B node5326 node5326Labels := by
  calc
    mixedMoment B raw15769 raw15769Labels = mixedMoment B raw15769step0 raw15769step0Labels := by
      have ha : raw15769step0 = (fun i j => raw15769 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15769step0 raw15769; decide +kernel
      have hl : raw15769step0Labels = raw15769Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15769 raw15769Labels permutation587 permutation3
    mixedMoment B raw15769step0 raw15769step0Labels = mixedMoment B raw15769step1 raw15769step1Labels := by
      have ha : raw15769step1 = -raw15769step0 := by apply Matrix.ext; change ∀ i j, raw15769step1 i j = -(raw15769step0 i j); unfold raw15769step1 raw15769step0; decide +kernel
      have hl : raw15769step1Labels = raw15769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15769step1 raw15769step1Labels = mixedMoment B raw15769step2 raw15769step2Labels := by
      have ha : raw15769step2 = raw15769step1 := by apply Matrix.ext; unfold raw15769step2 raw15769step1; decide +kernel
      have hl : raw15769step1Labels = labelEmbedding6 ∘ raw15769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15769step1 raw15769step1Labels raw15769step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5326 node5326Labels := by rfl

def raw15770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw15770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15770step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15770step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15770step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15770 raw15770Labels = mixedMoment B node5326 node5326Labels := by
  calc
    mixedMoment B raw15770 raw15770Labels = mixedMoment B raw15770step0 raw15770step0Labels := by
      have ha : raw15770step0 = (fun i j => raw15770 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15770step0 raw15770; decide +kernel
      have hl : raw15770step0Labels = raw15770Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15770 raw15770Labels permutation582 permutation3
    mixedMoment B raw15770step0 raw15770step0Labels = mixedMoment B raw15770step1 raw15770step1Labels := by
      have ha : raw15770step1 = -raw15770step0 := by apply Matrix.ext; change ∀ i j, raw15770step1 i j = -(raw15770step0 i j); unfold raw15770step1 raw15770step0; decide +kernel
      have hl : raw15770step1Labels = raw15770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15770step1 raw15770step1Labels = mixedMoment B raw15770step2 raw15770step2Labels := by
      have ha : raw15770step2 = raw15770step1 := by apply Matrix.ext; unfold raw15770step2 raw15770step1; decide +kernel
      have hl : raw15770step1Labels = labelEmbedding6 ∘ raw15770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15770step1 raw15770step1Labels raw15770step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5326 node5326Labels := by rfl

def raw15771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw15771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15771step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15771step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15771step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15771 raw15771Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw15771 raw15771Labels = mixedMoment B raw15771step0 raw15771step0Labels := by
      have ha : raw15771step0 = (fun i j => raw15771 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15771step0 raw15771; decide +kernel
      have hl : raw15771step0Labels = raw15771Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15771 raw15771Labels permutation681 permutation3
    mixedMoment B raw15771step0 raw15771step0Labels = mixedMoment B raw15771step1 raw15771step1Labels := by
      have ha : raw15771step1 = -raw15771step0 := by apply Matrix.ext; change ∀ i j, raw15771step1 i j = -(raw15771step0 i j); unfold raw15771step1 raw15771step0; decide +kernel
      have hl : raw15771step1Labels = raw15771step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15771step1 raw15771step1Labels = mixedMoment B raw15771step2 raw15771step2Labels := by
      have ha : raw15771step2 = raw15771step1 := by apply Matrix.ext; unfold raw15771step2 raw15771step1; decide +kernel
      have hl : raw15771step1Labels = labelEmbedding6 ∘ raw15771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15771step1 raw15771step1Labels raw15771step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

def raw15772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw15772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15772step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15772step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15772step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15772 raw15772Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw15772 raw15772Labels = mixedMoment B raw15772step0 raw15772step0Labels := by
      have ha : raw15772step0 = (fun i j => raw15772 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15772step0 raw15772; decide +kernel
      have hl : raw15772step0Labels = raw15772Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15772 raw15772Labels permutation686 permutation3
    mixedMoment B raw15772step0 raw15772step0Labels = mixedMoment B raw15772step1 raw15772step1Labels := by
      have ha : raw15772step1 = -raw15772step0 := by apply Matrix.ext; change ∀ i j, raw15772step1 i j = -(raw15772step0 i j); unfold raw15772step1 raw15772step0; decide +kernel
      have hl : raw15772step1Labels = raw15772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15772step1 raw15772step1Labels = mixedMoment B raw15772step2 raw15772step2Labels := by
      have ha : raw15772step2 = raw15772step1 := by apply Matrix.ext; unfold raw15772step2 raw15772step1; decide +kernel
      have hl : raw15772step1Labels = labelEmbedding6 ∘ raw15772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15772step1 raw15772step1Labels raw15772step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw15773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw15773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15773step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15773step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15773step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15773 raw15773Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw15773 raw15773Labels = mixedMoment B raw15773step0 raw15773step0Labels := by
      have ha : raw15773step0 = (fun i j => raw15773 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15773step0 raw15773; decide +kernel
      have hl : raw15773step0Labels = raw15773Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15773 raw15773Labels permutation680 permutation3
    mixedMoment B raw15773step0 raw15773step0Labels = mixedMoment B raw15773step1 raw15773step1Labels := by
      have ha : raw15773step1 = -raw15773step0 := by apply Matrix.ext; change ∀ i j, raw15773step1 i j = -(raw15773step0 i j); unfold raw15773step1 raw15773step0; decide +kernel
      have hl : raw15773step1Labels = raw15773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15773step1 raw15773step1Labels = mixedMoment B raw15773step2 raw15773step2Labels := by
      have ha : raw15773step2 = raw15773step1 := by apply Matrix.ext; unfold raw15773step2 raw15773step1; decide +kernel
      have hl : raw15773step1Labels = labelEmbedding6 ∘ raw15773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15773step1 raw15773step1Labels raw15773step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw15774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw15774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw15774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15774step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15774step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15774step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15774 raw15774Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw15774 raw15774Labels = mixedMoment B raw15774step0 raw15774step0Labels := by
      have hz : ∀ j, raw15774 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15774step0 = (fun i j => raw15774 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15774step0 raw15774; decide +kernel
      have hl : raw15774step0Labels = raw15774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15774 raw15774Labels permutation520 hz
    mixedMoment B raw15774step0 raw15774step0Labels = mixedMoment B raw15774step1 raw15774step1Labels := by
      have ha : raw15774step1 = (fun i j => raw15774step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15774step1 raw15774step0; decide +kernel
      have hl : raw15774step1Labels = raw15774step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15774step0 raw15774step0Labels permutation145 permutation3
    mixedMoment B raw15774step1 raw15774step1Labels = mixedMoment B raw15774step2 raw15774step2Labels := by
      have ha : raw15774step2 = -raw15774step1 := by apply Matrix.ext; change ∀ i j, raw15774step2 i j = -(raw15774step1 i j); unfold raw15774step2 raw15774step1; decide +kernel
      have hl : raw15774step2Labels = raw15774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15774step2 raw15774step2Labels = mixedMoment B raw15774step3 raw15774step3Labels := by
      have ha : raw15774step3 = raw15774step2 := by apply Matrix.ext; unfold raw15774step3 raw15774step2; decide +kernel
      have hl : raw15774step2Labels = labelEmbedding6 ∘ raw15774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15774step2 raw15774step2Labels raw15774step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw15775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15775 raw15775Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw15775 raw15775Labels = mixedMoment B raw15775step0 raw15775step0Labels := by
      have ha : raw15775step0 = (fun i j => raw15775 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15775step0 raw15775; decide +kernel
      have hl : raw15775step0Labels = raw15775Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15775 raw15775Labels permutation681 permutation3
    mixedMoment B raw15775step0 raw15775step0Labels = mixedMoment B raw15775step1 raw15775step1Labels := by
      have ha : raw15775step1 = -raw15775step0 := by apply Matrix.ext; change ∀ i j, raw15775step1 i j = -(raw15775step0 i j); unfold raw15775step1 raw15775step0; decide +kernel
      have hl : raw15775step1Labels = raw15775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw15776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15776step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15776 raw15776Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw15776 raw15776Labels = mixedMoment B raw15776step0 raw15776step0Labels := by
      have ha : raw15776step0 = (fun i j => raw15776 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15776step0 raw15776; decide +kernel
      have hl : raw15776step0Labels = raw15776Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15776 raw15776Labels permutation683 permutation3
    mixedMoment B raw15776step0 raw15776step0Labels = mixedMoment B raw15776step1 raw15776step1Labels := by
      have ha : raw15776step1 = -raw15776step0 := by apply Matrix.ext; change ∀ i j, raw15776step1 i j = -(raw15776step0 i j); unfold raw15776step1 raw15776step0; decide +kernel
      have hl : raw15776step1Labels = raw15776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw15777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15777 raw15777Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw15777 raw15777Labels = mixedMoment B raw15777step0 raw15777step0Labels := by
      have ha : raw15777step0 = (fun i j => raw15777 (permutation677 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15777step0 raw15777; decide +kernel
      have hl : raw15777step0Labels = raw15777Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15777 raw15777Labels permutation677 permutation3
    mixedMoment B raw15777step0 raw15777step0Labels = mixedMoment B raw15777step1 raw15777step1Labels := by
      have ha : raw15777step1 = -raw15777step0 := by apply Matrix.ext; change ∀ i j, raw15777step1 i j = -(raw15777step0 i j); unfold raw15777step1 raw15777step0; decide +kernel
      have hl : raw15777step1Labels = raw15777step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw15778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw15778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw15778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw15778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15778 raw15778Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw15778 raw15778Labels = mixedMoment B raw15778step0 raw15778step0Labels := by
      have hz : ∀ j, raw15778 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15778step0 = (fun i j => raw15778 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15778step0 raw15778; decide +kernel
      have hl : raw15778step0Labels = raw15778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15778 raw15778Labels permutation520 hz
    mixedMoment B raw15778step0 raw15778step0Labels = mixedMoment B raw15778step1 raw15778step1Labels := by
      have ha : raw15778step1 = (fun i j => raw15778step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15778step1 raw15778step0; decide +kernel
      have hl : raw15778step1Labels = raw15778step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15778step0 raw15778step0Labels permutation144 permutation3
    mixedMoment B raw15778step1 raw15778step1Labels = mixedMoment B raw15778step2 raw15778step2Labels := by
      have ha : raw15778step2 = -raw15778step1 := by apply Matrix.ext; change ∀ i j, raw15778step2 i j = -(raw15778step1 i j); unfold raw15778step2 raw15778step1; decide +kernel
      have hl : raw15778step2Labels = raw15778step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw15779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15779 raw15779Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw15779 raw15779Labels = mixedMoment B raw15779step0 raw15779step0Labels := by
      have ha : raw15779step0 = (fun i j => raw15779 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15779step0 raw15779; decide +kernel
      have hl : raw15779step0Labels = raw15779Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15779 raw15779Labels permutation271 permutation3
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw15780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15780 raw15780Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw15780 raw15780Labels = mixedMoment B raw15780step0 raw15780step0Labels := by
      have ha : raw15780step0 = (fun i j => raw15780 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15780step0 raw15780; decide +kernel
      have hl : raw15780step0Labels = raw15780Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15780 raw15780Labels permutation680 permutation3
    mixedMoment B raw15780step0 raw15780step0Labels = mixedMoment B raw15780step1 raw15780step1Labels := by
      have ha : raw15780step1 = -raw15780step0 := by apply Matrix.ext; change ∀ i j, raw15780step1 i j = -(raw15780step0 i j); unfold raw15780step1 raw15780step0; decide +kernel
      have hl : raw15780step1Labels = raw15780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw15781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw15781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw15781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15781 raw15781Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw15781 raw15781Labels = mixedMoment B raw15781step0 raw15781step0Labels := by
      have hz : ∀ j, raw15781 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15781step0 = (fun i j => raw15781 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15781step0 raw15781; decide +kernel
      have hl : raw15781step0Labels = raw15781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15781 raw15781Labels permutation520 hz
    mixedMoment B raw15781step0 raw15781step0Labels = mixedMoment B raw15781step1 raw15781step1Labels := by
      have ha : raw15781step1 = (fun i j => raw15781step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15781step1 raw15781step0; decide +kernel
      have hl : raw15781step1Labels = raw15781step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15781step0 raw15781step0Labels permutation145 permutation3
    mixedMoment B raw15781step1 raw15781step1Labels = mixedMoment B raw15781step2 raw15781step2Labels := by
      have ha : raw15781step2 = -raw15781step1 := by apply Matrix.ext; change ∀ i j, raw15781step2 i j = -(raw15781step1 i j); unfold raw15781step2 raw15781step1; decide +kernel
      have hl : raw15781step2Labels = raw15781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw15782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15782 raw15782Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw15782 raw15782Labels = mixedMoment B raw15782step0 raw15782step0Labels := by
      have ha : raw15782step0 = (fun i j => raw15782 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15782step0 raw15782; decide +kernel
      have hl : raw15782step0Labels = raw15782Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15782 raw15782Labels permutation265 permutation3
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw15783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15783step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15783 raw15783Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw15783 raw15783Labels = mixedMoment B raw15783step0 raw15783step0Labels := by
      have ha : raw15783step0 = (fun i j => raw15783 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15783step0 raw15783; decide +kernel
      have hl : raw15783step0Labels = raw15783Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15783 raw15783Labels permutation686 permutation3
    mixedMoment B raw15783step0 raw15783step0Labels = mixedMoment B raw15783step1 raw15783step1Labels := by
      have ha : raw15783step1 = -raw15783step0 := by apply Matrix.ext; change ∀ i j, raw15783step1 i j = -(raw15783step0 i j); unfold raw15783step1 raw15783step0; decide +kernel
      have hl : raw15783step1Labels = raw15783step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw15784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw15784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15784 raw15784Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw15784 raw15784Labels = mixedMoment B raw15784step0 raw15784step0Labels := by
      have hz : ∀ j, raw15784 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15784step0 = (fun i j => raw15784 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15784step0 raw15784; decide +kernel
      have hl : raw15784step0Labels = raw15784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15784 raw15784Labels permutation520 hz
    mixedMoment B raw15784step0 raw15784step0Labels = mixedMoment B raw15784step1 raw15784step1Labels := by
      have ha : raw15784step1 = (fun i j => raw15784step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15784step1 raw15784step0; decide +kernel
      have hl : raw15784step1Labels = raw15784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15784step0 raw15784step0Labels permutation151 permutation3
    mixedMoment B raw15784step1 raw15784step1Labels = mixedMoment B raw15784step2 raw15784step2Labels := by
      have ha : raw15784step2 = -raw15784step1 := by apply Matrix.ext; change ∀ i j, raw15784step2 i j = -(raw15784step1 i j); unfold raw15784step2 raw15784step1; decide +kernel
      have hl : raw15784step2Labels = raw15784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw15785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw15785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15785 raw15785Labels = mixedMoment B node3646 node3646Labels := by
  calc
    mixedMoment B raw15785 raw15785Labels = mixedMoment B raw15785step0 raw15785step0Labels := by
      have ha : raw15785step0 = (fun i j => raw15785 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15785step0 raw15785; decide +kernel
      have hl : raw15785step0Labels = raw15785Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15785 raw15785Labels permutation583 permutation3
    mixedMoment B raw15785step0 raw15785step0Labels = mixedMoment B raw15785step1 raw15785step1Labels := by
      have ha : raw15785step1 = -raw15785step0 := by apply Matrix.ext; change ∀ i j, raw15785step1 i j = -(raw15785step0 i j); unfold raw15785step1 raw15785step0; decide +kernel
      have hl : raw15785step1Labels = raw15785step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3646 node3646Labels := by rfl

def raw15786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw15786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15786 raw15786Labels = mixedMoment B node3653 node3653Labels := by
  calc
    mixedMoment B raw15786 raw15786Labels = mixedMoment B raw15786step0 raw15786step0Labels := by
      have ha : raw15786step0 = (fun i j => raw15786 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15786step0 raw15786; decide +kernel
      have hl : raw15786step0Labels = raw15786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15786 raw15786Labels permutation587 permutation3
    mixedMoment B raw15786step0 raw15786step0Labels = mixedMoment B raw15786step1 raw15786step1Labels := by
      have ha : raw15786step1 = -raw15786step0 := by apply Matrix.ext; change ∀ i j, raw15786step1 i j = -(raw15786step0 i j); unfold raw15786step1 raw15786step0; decide +kernel
      have hl : raw15786step1Labels = raw15786step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3653 node3653Labels := by rfl

def raw15787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw15787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15787 raw15787Labels = mixedMoment B node3653 node3653Labels := by
  calc
    mixedMoment B raw15787 raw15787Labels = mixedMoment B raw15787step0 raw15787step0Labels := by
      have ha : raw15787step0 = (fun i j => raw15787 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15787step0 raw15787; decide +kernel
      have hl : raw15787step0Labels = raw15787Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15787 raw15787Labels permutation582 permutation3
    mixedMoment B raw15787step0 raw15787step0Labels = mixedMoment B raw15787step1 raw15787step1Labels := by
      have ha : raw15787step1 = -raw15787step0 := by apply Matrix.ext; change ∀ i j, raw15787step1 i j = -(raw15787step0 i j); unfold raw15787step1 raw15787step0; decide +kernel
      have hl : raw15787step1Labels = raw15787step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3653 node3653Labels := by rfl

def raw15788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw15788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15788 raw15788Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw15788 raw15788Labels = mixedMoment B raw15788step0 raw15788step0Labels := by
      have ha : raw15788step0 = (fun i j => raw15788 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15788step0 raw15788; decide +kernel
      have hl : raw15788step0Labels = raw15788Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15788 raw15788Labels permutation681 permutation3
    mixedMoment B raw15788step0 raw15788step0Labels = mixedMoment B raw15788step1 raw15788step1Labels := by
      have ha : raw15788step1 = -raw15788step0 := by apply Matrix.ext; change ∀ i j, raw15788step1 i j = -(raw15788step0 i j); unfold raw15788step1 raw15788step0; decide +kernel
      have hl : raw15788step1Labels = raw15788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1900 node1900Labels := by rfl

def raw15789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw15789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15789 raw15789Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw15789 raw15789Labels = mixedMoment B raw15789step0 raw15789step0Labels := by
      have ha : raw15789step0 = (fun i j => raw15789 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15789step0 raw15789; decide +kernel
      have hl : raw15789step0Labels = raw15789Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15789 raw15789Labels permutation686 permutation3
    mixedMoment B raw15789step0 raw15789step0Labels = mixedMoment B raw15789step1 raw15789step1Labels := by
      have ha : raw15789step1 = -raw15789step0 := by apply Matrix.ext; change ∀ i j, raw15789step1 i j = -(raw15789step0 i j); unfold raw15789step1 raw15789step0; decide +kernel
      have hl : raw15789step1Labels = raw15789step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1913 node1913Labels := by rfl

def raw15790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw15790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15790 raw15790Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw15790 raw15790Labels = mixedMoment B raw15790step0 raw15790step0Labels := by
      have ha : raw15790step0 = (fun i j => raw15790 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15790step0 raw15790; decide +kernel
      have hl : raw15790step0Labels = raw15790Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15790 raw15790Labels permutation680 permutation3
    mixedMoment B raw15790step0 raw15790step0Labels = mixedMoment B raw15790step1 raw15790step1Labels := by
      have ha : raw15790step1 = -raw15790step0 := by apply Matrix.ext; change ∀ i j, raw15790step1 i j = -(raw15790step0 i j); unfold raw15790step1 raw15790step0; decide +kernel
      have hl : raw15790step1Labels = raw15790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1913 node1913Labels := by rfl

def raw15791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw15791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw15791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15791 raw15791Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw15791 raw15791Labels = mixedMoment B raw15791step0 raw15791step0Labels := by
      have hz : ∀ j, raw15791 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15791step0 = (fun i j => raw15791 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15791step0 raw15791; decide +kernel
      have hl : raw15791step0Labels = raw15791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15791 raw15791Labels permutation520 hz
    mixedMoment B raw15791step0 raw15791step0Labels = mixedMoment B raw15791step1 raw15791step1Labels := by
      have ha : raw15791step1 = (fun i j => raw15791step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15791step1 raw15791step0; decide +kernel
      have hl : raw15791step1Labels = raw15791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15791step0 raw15791step0Labels permutation145 permutation3
    mixedMoment B raw15791step1 raw15791step1Labels = mixedMoment B raw15791step2 raw15791step2Labels := by
      have ha : raw15791step2 = -raw15791step1 := by apply Matrix.ext; change ∀ i j, raw15791step2 i j = -(raw15791step1 i j); unfold raw15791step2 raw15791step1; decide +kernel
      have hl : raw15791step2Labels = raw15791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw15792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15792 raw15792Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw15792 raw15792Labels = mixedMoment B raw15792step0 raw15792step0Labels := by
      have ha : raw15792step0 = (fun i j => raw15792 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15792step0 raw15792; decide +kernel
      have hl : raw15792step0Labels = raw15792Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15792 raw15792Labels permutation681 permutation2
    mixedMoment B raw15792step0 raw15792step0Labels = mixedMoment B raw15792step1 raw15792step1Labels := by
      have ha : raw15792step1 = -raw15792step0 := by apply Matrix.ext; change ∀ i j, raw15792step1 i j = -(raw15792step0 i j); unfold raw15792step1 raw15792step0; decide +kernel
      have hl : raw15792step1Labels = raw15792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw15793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15793 raw15793Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw15793 raw15793Labels = mixedMoment B raw15793step0 raw15793step0Labels := by
      have ha : raw15793step0 = (fun i j => raw15793 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15793step0 raw15793; decide +kernel
      have hl : raw15793step0Labels = raw15793Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15793 raw15793Labels permutation683 permutation2
    mixedMoment B raw15793step0 raw15793step0Labels = mixedMoment B raw15793step1 raw15793step1Labels := by
      have ha : raw15793step1 = -raw15793step0 := by apply Matrix.ext; change ∀ i j, raw15793step1 i j = -(raw15793step0 i j); unfold raw15793step1 raw15793step0; decide +kernel
      have hl : raw15793step1Labels = raw15793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw15794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15794 raw15794Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw15794 raw15794Labels = mixedMoment B raw15794step0 raw15794step0Labels := by
      have ha : raw15794step0 = (fun i j => raw15794 (permutation677 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15794step0 raw15794; decide +kernel
      have hl : raw15794step0Labels = raw15794Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15794 raw15794Labels permutation677 permutation2
    mixedMoment B raw15794step0 raw15794step0Labels = mixedMoment B raw15794step1 raw15794step1Labels := by
      have ha : raw15794step1 = -raw15794step0 := by apply Matrix.ext; change ∀ i j, raw15794step1 i j = -(raw15794step0 i j); unfold raw15794step1 raw15794step0; decide +kernel
      have hl : raw15794step1Labels = raw15794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw15795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15795step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15795 raw15795Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw15795 raw15795Labels = mixedMoment B raw15795step0 raw15795step0Labels := by
      have ha : raw15795step0 = (fun i j => raw15795 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15795step0 raw15795; decide +kernel
      have hl : raw15795step0Labels = raw15795Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15795 raw15795Labels permutation668 permutation7
    mixedMoment B raw15795step0 raw15795step0Labels = mixedMoment B raw15795step1 raw15795step1Labels := by
      have ha : raw15795step1 = raw15795step0 := by apply Matrix.ext; unfold raw15795step1 raw15795step0; decide +kernel
      have hl : raw15795step0Labels = labelEmbedding10 ∘ raw15795step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15795step0 raw15795step0Labels raw15795step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw15796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15796step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15796 raw15796Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw15796 raw15796Labels = mixedMoment B raw15796step0 raw15796step0Labels := by
      have ha : raw15796step0 = (fun i j => raw15796 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15796step0 raw15796; decide +kernel
      have hl : raw15796step0Labels = raw15796Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15796 raw15796Labels permutation668 permutation7
    mixedMoment B raw15796step0 raw15796step0Labels = mixedMoment B raw15796step1 raw15796step1Labels := by
      have ha : raw15796step1 = raw15796step0 := by apply Matrix.ext; unfold raw15796step1 raw15796step0; decide +kernel
      have hl : raw15796step0Labels = labelEmbedding10 ∘ raw15796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15796step0 raw15796step0Labels raw15796step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw15797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15797 raw15797Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw15797 raw15797Labels = mixedMoment B raw15797step0 raw15797step0Labels := by
      have ha : raw15797step0 = (fun i j => raw15797 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15797step0 raw15797; decide +kernel
      have hl : raw15797step0Labels = raw15797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15797 raw15797Labels permutation152 permutation3
    mixedMoment B raw15797step0 raw15797step0Labels = mixedMoment B raw15797step1 raw15797step1Labels := by
      have ha : raw15797step1 = raw15797step0 := by apply Matrix.ext; unfold raw15797step1 raw15797step0; decide +kernel
      have hl : raw15797step0Labels = labelEmbedding6 ∘ raw15797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15797step0 raw15797step0Labels raw15797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw15798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15798step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15798 raw15798Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw15798 raw15798Labels = mixedMoment B raw15798step0 raw15798step0Labels := by
      have ha : raw15798step0 = (fun i j => raw15798 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15798step0 raw15798; decide +kernel
      have hl : raw15798step0Labels = raw15798Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15798 raw15798Labels permutation160 permutation3
    mixedMoment B raw15798step0 raw15798step0Labels = mixedMoment B raw15798step1 raw15798step1Labels := by
      have ha : raw15798step1 = raw15798step0 := by apply Matrix.ext; unfold raw15798step1 raw15798step0; decide +kernel
      have hl : raw15798step0Labels = labelEmbedding6 ∘ raw15798step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15798step0 raw15798step0Labels raw15798step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw15799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15799 raw15799Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw15799 raw15799Labels = mixedMoment B raw15799step0 raw15799step0Labels := by
      have ha : raw15799step0 = (fun i j => raw15799 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15799step0 raw15799; decide +kernel
      have hl : raw15799step0Labels = raw15799Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15799 raw15799Labels permutation680 permutation2
    mixedMoment B raw15799step0 raw15799step0Labels = mixedMoment B raw15799step1 raw15799step1Labels := by
      have ha : raw15799step1 = -raw15799step0 := by apply Matrix.ext; change ∀ i j, raw15799step1 i j = -(raw15799step0 i j); unfold raw15799step1 raw15799step0; decide +kernel
      have hl : raw15799step1Labels = raw15799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw15800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15800step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15800 raw15800Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw15800 raw15800Labels = mixedMoment B raw15800step0 raw15800step0Labels := by
      have ha : raw15800step0 = (fun i j => raw15800 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15800step0 raw15800; decide +kernel
      have hl : raw15800step0Labels = raw15800Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15800 raw15800Labels permutation166 permutation3
    mixedMoment B raw15800step0 raw15800step0Labels = mixedMoment B raw15800step1 raw15800step1Labels := by
      have ha : raw15800step1 = raw15800step0 := by apply Matrix.ext; unfold raw15800step1 raw15800step0; decide +kernel
      have hl : raw15800step0Labels = labelEmbedding6 ∘ raw15800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15800step0 raw15800step0Labels raw15800step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw15801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15801 raw15801Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw15801 raw15801Labels = mixedMoment B raw15801step0 raw15801step0Labels := by
      have ha : raw15801step0 = (fun i j => raw15801 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15801step0 raw15801; decide +kernel
      have hl : raw15801step0Labels = raw15801Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15801 raw15801Labels permutation163 permutation3
    mixedMoment B raw15801step0 raw15801step0Labels = mixedMoment B raw15801step1 raw15801step1Labels := by
      have ha : raw15801step1 = raw15801step0 := by apply Matrix.ext; unfold raw15801step1 raw15801step0; decide +kernel
      have hl : raw15801step0Labels = labelEmbedding6 ∘ raw15801step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15801step0 raw15801step0Labels raw15801step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw15802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15802step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15802step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15802 raw15802Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw15802 raw15802Labels = mixedMoment B raw15802step0 raw15802step0Labels := by
      have ha : raw15802step0 = (fun i j => raw15802 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15802step0 raw15802; decide +kernel
      have hl : raw15802step0Labels = raw15802Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15802 raw15802Labels permutation154 permutation3
    mixedMoment B raw15802step0 raw15802step0Labels = mixedMoment B raw15802step1 raw15802step1Labels := by
      have ha : raw15802step1 = raw15802step0 := by apply Matrix.ext; unfold raw15802step1 raw15802step0; decide +kernel
      have hl : raw15802step0Labels = labelEmbedding6 ∘ raw15802step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15802step0 raw15802step0Labels raw15802step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw15803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15803 raw15803Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw15803 raw15803Labels = mixedMoment B raw15803step0 raw15803step0Labels := by
      have ha : raw15803step0 = (fun i j => raw15803 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15803step0 raw15803; decide +kernel
      have hl : raw15803step0Labels = raw15803Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15803 raw15803Labels permutation686 permutation2
    mixedMoment B raw15803step0 raw15803step0Labels = mixedMoment B raw15803step1 raw15803step1Labels := by
      have ha : raw15803step1 = -raw15803step0 := by apply Matrix.ext; change ∀ i j, raw15803step1 i j = -(raw15803step0 i j); unfold raw15803step1 raw15803step0; decide +kernel
      have hl : raw15803step1Labels = raw15803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw15804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15804step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15804 raw15804Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw15804 raw15804Labels = mixedMoment B raw15804step0 raw15804step0Labels := by
      have ha : raw15804step0 = (fun i j => raw15804 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15804step0 raw15804; decide +kernel
      have hl : raw15804step0Labels = raw15804Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15804 raw15804Labels permutation164 permutation3
    mixedMoment B raw15804step0 raw15804step0Labels = mixedMoment B raw15804step1 raw15804step1Labels := by
      have ha : raw15804step1 = raw15804step0 := by apply Matrix.ext; unfold raw15804step1 raw15804step0; decide +kernel
      have hl : raw15804step0Labels = labelEmbedding6 ∘ raw15804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15804step0 raw15804step0Labels raw15804step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw15805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15805step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15805step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15805 raw15805Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw15805 raw15805Labels = mixedMoment B raw15805step0 raw15805step0Labels := by
      have ha : raw15805step0 = (fun i j => raw15805 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15805step0 raw15805; decide +kernel
      have hl : raw15805step0Labels = raw15805Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15805 raw15805Labels permutation157 permutation3
    mixedMoment B raw15805step0 raw15805step0Labels = mixedMoment B raw15805step1 raw15805step1Labels := by
      have ha : raw15805step1 = raw15805step0 := by apply Matrix.ext; unfold raw15805step1 raw15805step0; decide +kernel
      have hl : raw15805step0Labels = labelEmbedding6 ∘ raw15805step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15805step0 raw15805step0Labels raw15805step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw15806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15806 raw15806Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw15806 raw15806Labels = mixedMoment B raw15806step0 raw15806step0Labels := by
      have ha : raw15806step0 = (fun i j => raw15806 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15806step0 raw15806; decide +kernel
      have hl : raw15806step0Labels = raw15806Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15806 raw15806Labels permutation681 permutation2
    mixedMoment B raw15806step0 raw15806step0Labels = mixedMoment B raw15806step1 raw15806step1Labels := by
      have ha : raw15806step1 = -raw15806step0 := by apply Matrix.ext; change ∀ i j, raw15806step1 i j = -(raw15806step0 i j); unfold raw15806step1 raw15806step0; decide +kernel
      have hl : raw15806step1Labels = raw15806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5348 node5348Labels := by rfl

def raw15807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15807 raw15807Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw15807 raw15807Labels = mixedMoment B raw15807step0 raw15807step0Labels := by
      have ha : raw15807step0 = (fun i j => raw15807 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15807step0 raw15807; decide +kernel
      have hl : raw15807step0Labels = raw15807Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15807 raw15807Labels permutation686 permutation2
    mixedMoment B raw15807step0 raw15807step0Labels = mixedMoment B raw15807step1 raw15807step1Labels := by
      have ha : raw15807step1 = -raw15807step0 := by apply Matrix.ext; change ∀ i j, raw15807step1 i j = -(raw15807step0 i j); unfold raw15807step1 raw15807step0; decide +kernel
      have hl : raw15807step1Labels = raw15807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw15808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15808 raw15808Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw15808 raw15808Labels = mixedMoment B raw15808step0 raw15808step0Labels := by
      have ha : raw15808step0 = (fun i j => raw15808 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15808step0 raw15808; decide +kernel
      have hl : raw15808step0Labels = raw15808Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15808 raw15808Labels permutation680 permutation2
    mixedMoment B raw15808step0 raw15808step0Labels = mixedMoment B raw15808step1 raw15808step1Labels := by
      have ha : raw15808step1 = -raw15808step0 := by apply Matrix.ext; change ∀ i j, raw15808step1 i j = -(raw15808step0 i j); unfold raw15808step1 raw15808step0; decide +kernel
      have hl : raw15808step1Labels = raw15808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw15809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw15809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15809step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15809 raw15809Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw15809 raw15809Labels = mixedMoment B raw15809step0 raw15809step0Labels := by
      have ha : raw15809step0 = (fun i j => raw15809 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15809step0 raw15809; decide +kernel
      have hl : raw15809step0Labels = raw15809Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15809 raw15809Labels permutation153 permutation3
    mixedMoment B raw15809step0 raw15809step0Labels = mixedMoment B raw15809step1 raw15809step1Labels := by
      have ha : raw15809step1 = raw15809step0 := by apply Matrix.ext; unfold raw15809step1 raw15809step0; decide +kernel
      have hl : raw15809step0Labels = labelEmbedding6 ∘ raw15809step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15809step0 raw15809step0Labels raw15809step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw15810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15810 raw15810Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw15810 raw15810Labels = mixedMoment B raw15810step0 raw15810step0Labels := by
      have ha : raw15810step0 = (fun i j => raw15810 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15810step0 raw15810; decide +kernel
      have hl : raw15810step0Labels = raw15810Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15810 raw15810Labels permutation681 permutation2
    mixedMoment B raw15810step0 raw15810step0Labels = mixedMoment B raw15810step1 raw15810step1Labels := by
      have ha : raw15810step1 = -raw15810step0 := by apply Matrix.ext; change ∀ i j, raw15810step1 i j = -(raw15810step0 i j); unfold raw15810step1 raw15810step0; decide +kernel
      have hl : raw15810step1Labels = raw15810step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw15811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15811 raw15811Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw15811 raw15811Labels = mixedMoment B raw15811step0 raw15811step0Labels := by
      have ha : raw15811step0 = (fun i j => raw15811 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15811step0 raw15811; decide +kernel
      have hl : raw15811step0Labels = raw15811Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15811 raw15811Labels permutation686 permutation2
    mixedMoment B raw15811step0 raw15811step0Labels = mixedMoment B raw15811step1 raw15811step1Labels := by
      have ha : raw15811step1 = -raw15811step0 := by apply Matrix.ext; change ∀ i j, raw15811step1 i j = -(raw15811step0 i j); unfold raw15811step1 raw15811step0; decide +kernel
      have hl : raw15811step1Labels = raw15811step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw15812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15812 raw15812Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw15812 raw15812Labels = mixedMoment B raw15812step0 raw15812step0Labels := by
      have ha : raw15812step0 = (fun i j => raw15812 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15812step0 raw15812; decide +kernel
      have hl : raw15812step0Labels = raw15812Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15812 raw15812Labels permutation680 permutation2
    mixedMoment B raw15812step0 raw15812step0Labels = mixedMoment B raw15812step1 raw15812step1Labels := by
      have ha : raw15812step1 = -raw15812step0 := by apply Matrix.ext; change ∀ i j, raw15812step1 i j = -(raw15812step0 i j); unfold raw15812step1 raw15812step0; decide +kernel
      have hl : raw15812step1Labels = raw15812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw15813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw15813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15813 raw15813Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw15813 raw15813Labels = mixedMoment B raw15813step0 raw15813step0Labels := by
      have ha : raw15813step0 = (fun i j => raw15813 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15813step0 raw15813; decide +kernel
      have hl : raw15813step0Labels = raw15813Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15813 raw15813Labels permutation682 permutation2
    mixedMoment B raw15813step0 raw15813step0Labels = mixedMoment B raw15813step1 raw15813step1Labels := by
      have ha : raw15813step1 = -raw15813step0 := by apply Matrix.ext; change ∀ i j, raw15813step1 i j = -(raw15813step0 i j); unfold raw15813step1 raw15813step0; decide +kernel
      have hl : raw15813step1Labels = raw15813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw15814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15814 raw15814Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw15814 raw15814Labels = mixedMoment B raw15814step0 raw15814step0Labels := by
      have ha : raw15814step0 = (fun i j => raw15814 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15814step0 raw15814; decide +kernel
      have hl : raw15814step0Labels = raw15814Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15814 raw15814Labels permutation265 permutation3
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw15815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15815 raw15815Labels = mixedMoment B node4038 node4038Labels := by
  calc
    mixedMoment B raw15815 raw15815Labels = mixedMoment B raw15815step0 raw15815step0Labels := by
      have ha : raw15815step0 = (fun i j => raw15815 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15815step0 raw15815; decide +kernel
      have hl : raw15815step0Labels = raw15815Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15815 raw15815Labels permutation686 permutation3
    mixedMoment B raw15815step0 raw15815step0Labels = mixedMoment B raw15815step1 raw15815step1Labels := by
      have ha : raw15815step1 = -raw15815step0 := by apply Matrix.ext; change ∀ i j, raw15815step1 i j = -(raw15815step0 i j); unfold raw15815step1 raw15815step0; decide +kernel
      have hl : raw15815step1Labels = raw15815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4038 node4038Labels := by rfl

def raw15816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15816 raw15816Labels = mixedMoment B node4038 node4038Labels := by
  calc
    mixedMoment B raw15816 raw15816Labels = mixedMoment B raw15816step0 raw15816step0Labels := by
      have ha : raw15816step0 = (fun i j => raw15816 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15816step0 raw15816; decide +kernel
      have hl : raw15816step0Labels = raw15816Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15816 raw15816Labels permutation680 permutation3
    mixedMoment B raw15816step0 raw15816step0Labels = mixedMoment B raw15816step1 raw15816step1Labels := by
      have ha : raw15816step1 = -raw15816step0 := by apply Matrix.ext; change ∀ i j, raw15816step1 i j = -(raw15816step0 i j); unfold raw15816step1 raw15816step0; decide +kernel
      have hl : raw15816step1Labels = raw15816step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4038 node4038Labels := by rfl

def raw15817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15817 raw15817Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw15817 raw15817Labels = mixedMoment B raw15817step0 raw15817step0Labels := by
      have ha : raw15817step0 = (fun i j => raw15817 (permutation665 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15817step0 raw15817; decide +kernel
      have hl : raw15817step0Labels = raw15817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15817 raw15817Labels permutation665 permutation6
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw15818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15818 raw15818Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw15818 raw15818Labels = mixedMoment B raw15818step0 raw15818step0Labels := by
      have ha : raw15818step0 = (fun i j => raw15818 (permutation665 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15818step0 raw15818; decide +kernel
      have hl : raw15818step0Labels = raw15818Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15818 raw15818Labels permutation665 permutation6
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw15819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15819 raw15819Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw15819 raw15819Labels = mixedMoment B raw15819step0 raw15819step0Labels := by
      have ha : raw15819step0 = (fun i j => raw15819 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15819step0 raw15819; decide +kernel
      have hl : raw15819step0Labels = raw15819Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15819 raw15819Labels permutation152 permutation3
    _ = mixedMoment B node2233 node2233Labels := by rfl

def raw15820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15820 raw15820Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw15820 raw15820Labels = mixedMoment B raw15820step0 raw15820step0Labels := by
      have ha : raw15820step0 = (fun i j => raw15820 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15820step0 raw15820; decide +kernel
      have hl : raw15820step0Labels = raw15820Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15820 raw15820Labels permutation160 permutation3
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw15821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15821 raw15821Labels = mixedMoment B node3822 node3822Labels := by
  calc
    mixedMoment B raw15821 raw15821Labels = mixedMoment B raw15821step0 raw15821step0Labels := by
      have ha : raw15821step0 = (fun i j => raw15821 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15821step0 raw15821; decide +kernel
      have hl : raw15821step0Labels = raw15821Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15821 raw15821Labels permutation160 permutation3
    _ = mixedMoment B node3822 node3822Labels := by rfl

def raw15822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15822 raw15822Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw15822 raw15822Labels = mixedMoment B raw15822step0 raw15822step0Labels := by
      have ha : raw15822step0 = (fun i j => raw15822 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15822step0 raw15822; decide +kernel
      have hl : raw15822step0Labels = raw15822Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15822 raw15822Labels permutation166 permutation3
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw15823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15823 raw15823Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw15823 raw15823Labels = mixedMoment B raw15823step0 raw15823step0Labels := by
      have ha : raw15823step0 = (fun i j => raw15823 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15823step0 raw15823; decide +kernel
      have hl : raw15823step0Labels = raw15823Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15823 raw15823Labels permutation163 permutation3
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw15824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15824 raw15824Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw15824 raw15824Labels = mixedMoment B raw15824step0 raw15824step0Labels := by
      have ha : raw15824step0 = (fun i j => raw15824 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15824step0 raw15824; decide +kernel
      have hl : raw15824step0Labels = raw15824Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15824 raw15824Labels permutation154 permutation3
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw15825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15825 raw15825Labels = mixedMoment B node3822 node3822Labels := by
  calc
    mixedMoment B raw15825 raw15825Labels = mixedMoment B raw15825step0 raw15825step0Labels := by
      have ha : raw15825step0 = (fun i j => raw15825 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15825step0 raw15825; decide +kernel
      have hl : raw15825step0Labels = raw15825Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15825 raw15825Labels permutation154 permutation3
    _ = mixedMoment B node3822 node3822Labels := by rfl

def raw15826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15826 raw15826Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw15826 raw15826Labels = mixedMoment B raw15826step0 raw15826step0Labels := by
      have ha : raw15826step0 = (fun i j => raw15826 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15826step0 raw15826; decide +kernel
      have hl : raw15826step0Labels = raw15826Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15826 raw15826Labels permutation164 permutation3
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw15827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15827 raw15827Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw15827 raw15827Labels = mixedMoment B raw15827step0 raw15827step0Labels := by
      have ha : raw15827step0 = (fun i j => raw15827 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15827step0 raw15827; decide +kernel
      have hl : raw15827step0Labels = raw15827Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15827 raw15827Labels permutation157 permutation3
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw15828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15828 raw15828Labels = mixedMoment B node3685 node3685Labels := by
  calc
    mixedMoment B raw15828 raw15828Labels = mixedMoment B raw15828step0 raw15828step0Labels := by
      have ha : raw15828step0 = (fun i j => raw15828 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15828step0 raw15828; decide +kernel
      have hl : raw15828step0Labels = raw15828Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15828 raw15828Labels permutation153 permutation3
    _ = mixedMoment B node3685 node3685Labels := by rfl

def raw15829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15829 raw15829Labels = mixedMoment B node3818 node3818Labels := by
  calc
    mixedMoment B raw15829 raw15829Labels = mixedMoment B raw15829step0 raw15829step0Labels := by
      have ha : raw15829step0 = (fun i j => raw15829 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15829step0 raw15829; decide +kernel
      have hl : raw15829step0Labels = raw15829Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15829 raw15829Labels permutation153 permutation3
    _ = mixedMoment B node3818 node3818Labels := by rfl

def raw15830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15830 raw15830Labels = mixedMoment B node3818 node3818Labels := by
  calc
    mixedMoment B raw15830 raw15830Labels = mixedMoment B raw15830step0 raw15830step0Labels := by
      have ha : raw15830step0 = (fun i j => raw15830 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15830step0 raw15830; decide +kernel
      have hl : raw15830step0Labels = raw15830Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15830 raw15830Labels permutation159 permutation3
    _ = mixedMoment B node3818 node3818Labels := by rfl

def raw15831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw15831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15831 raw15831Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw15831 raw15831Labels = mixedMoment B raw15831step0 raw15831step0Labels := by
      have ha : raw15831step0 = (fun i j => raw15831 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15831step0 raw15831; decide +kernel
      have hl : raw15831step0Labels = raw15831Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15831 raw15831Labels permutation153 permutation3
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw15832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15832 raw15832Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw15832 raw15832Labels = mixedMoment B raw15832step0 raw15832step0Labels := by
      have ha : raw15832step0 = (fun i j => raw15832 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15832step0 raw15832; decide +kernel
      have hl : raw15832step0Labels = raw15832Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15832 raw15832Labels permutation682 permutation3
    mixedMoment B raw15832step0 raw15832step0Labels = mixedMoment B raw15832step1 raw15832step1Labels := by
      have ha : raw15832step1 = -raw15832step0 := by apply Matrix.ext; change ∀ i j, raw15832step1 i j = -(raw15832step0 i j); unfold raw15832step1 raw15832step0; decide +kernel
      have hl : raw15832step1Labels = raw15832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2981 node2981Labels := by rfl

def raw15833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15833 raw15833Labels = mixedMoment B node2986 node2986Labels := by
  calc
    mixedMoment B raw15833 raw15833Labels = mixedMoment B raw15833step0 raw15833step0Labels := by
      have ha : raw15833step0 = (fun i j => raw15833 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15833step0 raw15833; decide +kernel
      have hl : raw15833step0Labels = raw15833Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15833 raw15833Labels permutation686 permutation3
    mixedMoment B raw15833step0 raw15833step0Labels = mixedMoment B raw15833step1 raw15833step1Labels := by
      have ha : raw15833step1 = -raw15833step0 := by apply Matrix.ext; change ∀ i j, raw15833step1 i j = -(raw15833step0 i j); unfold raw15833step1 raw15833step0; decide +kernel
      have hl : raw15833step1Labels = raw15833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2986 node2986Labels := by rfl

def raw15834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15834 raw15834Labels = mixedMoment B node2986 node2986Labels := by
  calc
    mixedMoment B raw15834 raw15834Labels = mixedMoment B raw15834step0 raw15834step0Labels := by
      have ha : raw15834step0 = (fun i j => raw15834 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15834step0 raw15834; decide +kernel
      have hl : raw15834step0Labels = raw15834Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15834 raw15834Labels permutation680 permutation3
    mixedMoment B raw15834step0 raw15834step0Labels = mixedMoment B raw15834step1 raw15834step1Labels := by
      have ha : raw15834step1 = -raw15834step0 := by apply Matrix.ext; change ∀ i j, raw15834step1 i j = -(raw15834step0 i j); unfold raw15834step1 raw15834step0; decide +kernel
      have hl : raw15834step1Labels = raw15834step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2986 node2986Labels := by rfl

def raw15835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw15835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15835 raw15835Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw15835 raw15835Labels = mixedMoment B raw15835step0 raw15835step0Labels := by
      have ha : raw15835step0 = (fun i j => raw15835 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15835step0 raw15835; decide +kernel
      have hl : raw15835step0Labels = raw15835Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15835 raw15835Labels permutation640 permutation3
    mixedMoment B raw15835step0 raw15835step0Labels = mixedMoment B raw15835step1 raw15835step1Labels := by
      have ha : raw15835step1 = -raw15835step0 := by apply Matrix.ext; change ∀ i j, raw15835step1 i j = -(raw15835step0 i j); unfold raw15835step1 raw15835step0; decide +kernel
      have hl : raw15835step1Labels = raw15835step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw15836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15836 raw15836Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw15836 raw15836Labels = mixedMoment B raw15836step0 raw15836step0Labels := by
      have ha : raw15836step0 = (fun i j => raw15836 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15836step0 raw15836; decide +kernel
      have hl : raw15836step0Labels = raw15836Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15836 raw15836Labels permutation668 permutation7
    mixedMoment B raw15836step0 raw15836step0Labels = mixedMoment B raw15836step1 raw15836step1Labels := by
      have ha : raw15836step1 = raw15836step0 := by apply Matrix.ext; unfold raw15836step1 raw15836step0; decide +kernel
      have hl : raw15836step0Labels = labelEmbedding1 ∘ raw15836step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15836step0 raw15836step0Labels raw15836step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw15837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15837step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15837 raw15837Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw15837 raw15837Labels = mixedMoment B raw15837step0 raw15837step0Labels := by
      have ha : raw15837step0 = (fun i j => raw15837 (permutation669 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15837step0 raw15837; decide +kernel
      have hl : raw15837step0Labels = raw15837Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15837 raw15837Labels permutation669 permutation7
    mixedMoment B raw15837step0 raw15837step0Labels = mixedMoment B raw15837step1 raw15837step1Labels := by
      have ha : raw15837step1 = raw15837step0 := by apply Matrix.ext; unfold raw15837step1 raw15837step0; decide +kernel
      have hl : raw15837step0Labels = labelEmbedding1 ∘ raw15837step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15837step0 raw15837step0Labels raw15837step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw15838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15838 raw15838Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw15838 raw15838Labels = mixedMoment B raw15838step0 raw15838step0Labels := by
      have ha : raw15838step0 = (fun i j => raw15838 (permutation667 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15838step0 raw15838; decide +kernel
      have hl : raw15838step0Labels = raw15838Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15838 raw15838Labels permutation667 permutation7
    mixedMoment B raw15838step0 raw15838step0Labels = mixedMoment B raw15838step1 raw15838step1Labels := by
      have ha : raw15838step1 = raw15838step0 := by apply Matrix.ext; unfold raw15838step1 raw15838step0; decide +kernel
      have hl : raw15838step0Labels = labelEmbedding1 ∘ raw15838step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15838step0 raw15838step0Labels raw15838step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw15839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15839step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15839 raw15839Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw15839 raw15839Labels = mixedMoment B raw15839step0 raw15839step0Labels := by
      have ha : raw15839step0 = (fun i j => raw15839 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15839step0 raw15839; decide +kernel
      have hl : raw15839step0Labels = raw15839Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15839 raw15839Labels permutation668 permutation7
    mixedMoment B raw15839step0 raw15839step0Labels = mixedMoment B raw15839step1 raw15839step1Labels := by
      have ha : raw15839step1 = raw15839step0 := by apply Matrix.ext; unfold raw15839step1 raw15839step0; decide +kernel
      have hl : raw15839step0Labels = labelEmbedding1 ∘ raw15839step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15839step0 raw15839step0Labels raw15839step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw15840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15840step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15840step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15840 raw15840Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw15840 raw15840Labels = mixedMoment B raw15840step0 raw15840step0Labels := by
      have ha : raw15840step0 = (fun i j => raw15840 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15840step0 raw15840; decide +kernel
      have hl : raw15840step0Labels = raw15840Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15840 raw15840Labels permutation668 permutation7
    mixedMoment B raw15840step0 raw15840step0Labels = mixedMoment B raw15840step1 raw15840step1Labels := by
      have ha : raw15840step1 = raw15840step0 := by apply Matrix.ext; unfold raw15840step1 raw15840step0; decide +kernel
      have hl : raw15840step0Labels = labelEmbedding1 ∘ raw15840step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15840step0 raw15840step0Labels raw15840step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw15841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw15841step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15841step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15841 raw15841Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw15841 raw15841Labels = mixedMoment B raw15841step0 raw15841step0Labels := by
      have ha : raw15841step0 = (fun i j => raw15841 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15841step0 raw15841; decide +kernel
      have hl : raw15841step0Labels = raw15841Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15841 raw15841Labels permutation240 permutation5
    mixedMoment B raw15841step0 raw15841step0Labels = mixedMoment B raw15841step1 raw15841step1Labels := by
      have ha : raw15841step1 = -raw15841step0 := by apply Matrix.ext; change ∀ i j, raw15841step1 i j = -(raw15841step0 i j); unfold raw15841step1 raw15841step0; decide +kernel
      have hl : raw15841step1Labels = raw15841step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15841step1 raw15841step1Labels = mixedMoment B raw15841step2 raw15841step2Labels := by
      have ha : raw15841step2 = raw15841step1 := by apply Matrix.ext; unfold raw15841step2 raw15841step1; decide +kernel
      have hl : raw15841step1Labels = labelEmbedding1 ∘ raw15841step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15841step1 raw15841step1Labels raw15841step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw15842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15842step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15842 raw15842Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw15842 raw15842Labels = mixedMoment B raw15842step0 raw15842step0Labels := by
      have ha : raw15842step0 = (fun i j => raw15842 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15842step0 raw15842; decide +kernel
      have hl : raw15842step0Labels = raw15842Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15842 raw15842Labels permutation169 permutation5
    mixedMoment B raw15842step0 raw15842step0Labels = mixedMoment B raw15842step1 raw15842step1Labels := by
      have ha : raw15842step1 = -raw15842step0 := by apply Matrix.ext; change ∀ i j, raw15842step1 i j = -(raw15842step0 i j); unfold raw15842step1 raw15842step0; decide +kernel
      have hl : raw15842step1Labels = raw15842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15842step1 raw15842step1Labels = mixedMoment B raw15842step2 raw15842step2Labels := by
      have ha : raw15842step2 = raw15842step1 := by apply Matrix.ext; unfold raw15842step2 raw15842step1; decide +kernel
      have hl : raw15842step1Labels = labelEmbedding1 ∘ raw15842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15842step1 raw15842step1Labels raw15842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw15843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15843step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15843 raw15843Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw15843 raw15843Labels = mixedMoment B raw15843step0 raw15843step0Labels := by
      have ha : raw15843step0 = (fun i j => raw15843 (permutation667 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15843step0 raw15843; decide +kernel
      have hl : raw15843step0Labels = raw15843Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15843 raw15843Labels permutation667 permutation7
    mixedMoment B raw15843step0 raw15843step0Labels = mixedMoment B raw15843step1 raw15843step1Labels := by
      have ha : raw15843step1 = raw15843step0 := by apply Matrix.ext; unfold raw15843step1 raw15843step0; decide +kernel
      have hl : raw15843step0Labels = labelEmbedding1 ∘ raw15843step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15843step0 raw15843step0Labels raw15843step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

def raw15844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15844step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15844 raw15844Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw15844 raw15844Labels = mixedMoment B raw15844step0 raw15844step0Labels := by
      have ha : raw15844step0 = (fun i j => raw15844 (permutation229 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15844step0 raw15844; decide +kernel
      have hl : raw15844step0Labels = raw15844Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15844 raw15844Labels permutation229 permutation5
    mixedMoment B raw15844step0 raw15844step0Labels = mixedMoment B raw15844step1 raw15844step1Labels := by
      have ha : raw15844step1 = -raw15844step0 := by apply Matrix.ext; change ∀ i j, raw15844step1 i j = -(raw15844step0 i j); unfold raw15844step1 raw15844step0; decide +kernel
      have hl : raw15844step1Labels = raw15844step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15844step1 raw15844step1Labels = mixedMoment B raw15844step2 raw15844step2Labels := by
      have ha : raw15844step2 = raw15844step1 := by apply Matrix.ext; unfold raw15844step2 raw15844step1; decide +kernel
      have hl : raw15844step1Labels = labelEmbedding1 ∘ raw15844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15844step1 raw15844step1Labels raw15844step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw15845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15845step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15845step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15845 raw15845Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw15845 raw15845Labels = mixedMoment B raw15845step0 raw15845step0Labels := by
      have ha : raw15845step0 = (fun i j => raw15845 (permutation251 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15845step0 raw15845; decide +kernel
      have hl : raw15845step0Labels = raw15845Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15845 raw15845Labels permutation251 permutation5
    mixedMoment B raw15845step0 raw15845step0Labels = mixedMoment B raw15845step1 raw15845step1Labels := by
      have ha : raw15845step1 = -raw15845step0 := by apply Matrix.ext; change ∀ i j, raw15845step1 i j = -(raw15845step0 i j); unfold raw15845step1 raw15845step0; decide +kernel
      have hl : raw15845step1Labels = raw15845step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15845step1 raw15845step1Labels = mixedMoment B raw15845step2 raw15845step2Labels := by
      have ha : raw15845step2 = raw15845step1 := by apply Matrix.ext; unfold raw15845step2 raw15845step1; decide +kernel
      have hl : raw15845step1Labels = labelEmbedding1 ∘ raw15845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15845step1 raw15845step1Labels raw15845step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw15846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15846step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15846 raw15846Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw15846 raw15846Labels = mixedMoment B raw15846step0 raw15846step0Labels := by
      have ha : raw15846step0 = (fun i j => raw15846 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15846step0 raw15846; decide +kernel
      have hl : raw15846step0Labels = raw15846Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15846 raw15846Labels permutation168 permutation5
    mixedMoment B raw15846step0 raw15846step0Labels = mixedMoment B raw15846step1 raw15846step1Labels := by
      have ha : raw15846step1 = -raw15846step0 := by apply Matrix.ext; change ∀ i j, raw15846step1 i j = -(raw15846step0 i j); unfold raw15846step1 raw15846step0; decide +kernel
      have hl : raw15846step1Labels = raw15846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15846step1 raw15846step1Labels = mixedMoment B raw15846step2 raw15846step2Labels := by
      have ha : raw15846step2 = raw15846step1 := by apply Matrix.ext; unfold raw15846step2 raw15846step1; decide +kernel
      have hl : raw15846step1Labels = labelEmbedding1 ∘ raw15846step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15846step1 raw15846step1Labels raw15846step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw15847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15847Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15847step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15847 raw15847Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw15847 raw15847Labels = mixedMoment B raw15847step0 raw15847step0Labels := by
      have ha : raw15847step0 = (fun i j => raw15847 (permutation669 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15847step0 raw15847; decide +kernel
      have hl : raw15847step0Labels = raw15847Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15847 raw15847Labels permutation669 permutation7
    mixedMoment B raw15847step0 raw15847step0Labels = mixedMoment B raw15847step1 raw15847step1Labels := by
      have ha : raw15847step1 = raw15847step0 := by apply Matrix.ext; unfold raw15847step1 raw15847step0; decide +kernel
      have hl : raw15847step0Labels = labelEmbedding1 ∘ raw15847step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15847step0 raw15847step0Labels raw15847step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

def raw15848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw15848Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15848step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15848step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15848 raw15848Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw15848 raw15848Labels = mixedMoment B raw15848step0 raw15848step0Labels := by
      have ha : raw15848step0 = (fun i j => raw15848 (permutation228 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15848step0 raw15848; decide +kernel
      have hl : raw15848step0Labels = raw15848Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15848 raw15848Labels permutation228 permutation5
    mixedMoment B raw15848step0 raw15848step0Labels = mixedMoment B raw15848step1 raw15848step1Labels := by
      have ha : raw15848step1 = -raw15848step0 := by apply Matrix.ext; change ∀ i j, raw15848step1 i j = -(raw15848step0 i j); unfold raw15848step1 raw15848step0; decide +kernel
      have hl : raw15848step1Labels = raw15848step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15848step1 raw15848step1Labels = mixedMoment B raw15848step2 raw15848step2Labels := by
      have ha : raw15848step2 = raw15848step1 := by apply Matrix.ext; unfold raw15848step2 raw15848step1; decide +kernel
      have hl : raw15848step1Labels = labelEmbedding1 ∘ raw15848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15848step1 raw15848step1Labels raw15848step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw15849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15849Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15849step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15849step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15849 raw15849Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw15849 raw15849Labels = mixedMoment B raw15849step0 raw15849step0Labels := by
      have ha : raw15849step0 = (fun i j => raw15849 (permutation250 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15849step0 raw15849; decide +kernel
      have hl : raw15849step0Labels = raw15849Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15849 raw15849Labels permutation250 permutation5
    mixedMoment B raw15849step0 raw15849step0Labels = mixedMoment B raw15849step1 raw15849step1Labels := by
      have ha : raw15849step1 = -raw15849step0 := by apply Matrix.ext; change ∀ i j, raw15849step1 i j = -(raw15849step0 i j); unfold raw15849step1 raw15849step0; decide +kernel
      have hl : raw15849step1Labels = raw15849step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15849step1 raw15849step1Labels = mixedMoment B raw15849step2 raw15849step2Labels := by
      have ha : raw15849step2 = raw15849step1 := by apply Matrix.ext; unfold raw15849step2 raw15849step1; decide +kernel
      have hl : raw15849step1Labels = labelEmbedding1 ∘ raw15849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15849step1 raw15849step1Labels raw15849step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw15850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15850Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15850step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15850step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15850 raw15850Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw15850 raw15850Labels = mixedMoment B raw15850step0 raw15850step0Labels := by
      have ha : raw15850step0 = (fun i j => raw15850 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15850step0 raw15850; decide +kernel
      have hl : raw15850step0Labels = raw15850Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15850 raw15850Labels permutation170 permutation5
    mixedMoment B raw15850step0 raw15850step0Labels = mixedMoment B raw15850step1 raw15850step1Labels := by
      have ha : raw15850step1 = -raw15850step0 := by apply Matrix.ext; change ∀ i j, raw15850step1 i j = -(raw15850step0 i j); unfold raw15850step1 raw15850step0; decide +kernel
      have hl : raw15850step1Labels = raw15850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15850step1 raw15850step1Labels = mixedMoment B raw15850step2 raw15850step2Labels := by
      have ha : raw15850step2 = raw15850step1 := by apply Matrix.ext; unfold raw15850step2 raw15850step1; decide +kernel
      have hl : raw15850step1Labels = labelEmbedding1 ∘ raw15850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15850step1 raw15850step1Labels raw15850step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

def raw15851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15851Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15851step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15851 raw15851Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw15851 raw15851Labels = mixedMoment B raw15851step0 raw15851step0Labels := by
      have ha : raw15851step0 = (fun i j => raw15851 (permutation669 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15851step0 raw15851; decide +kernel
      have hl : raw15851step0Labels = raw15851Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15851 raw15851Labels permutation669 permutation7
    mixedMoment B raw15851step0 raw15851step0Labels = mixedMoment B raw15851step1 raw15851step1Labels := by
      have ha : raw15851step1 = raw15851step0 := by apply Matrix.ext; unfold raw15851step1 raw15851step0; decide +kernel
      have hl : raw15851step0Labels = labelEmbedding1 ∘ raw15851step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15851step0 raw15851step0Labels raw15851step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw15852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15852step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15852 raw15852Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw15852 raw15852Labels = mixedMoment B raw15852step0 raw15852step0Labels := by
      have ha : raw15852step0 = (fun i j => raw15852 (permutation667 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15852step0 raw15852; decide +kernel
      have hl : raw15852step0Labels = raw15852Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15852 raw15852Labels permutation667 permutation7
    mixedMoment B raw15852step0 raw15852step0Labels = mixedMoment B raw15852step1 raw15852step1Labels := by
      have ha : raw15852step1 = raw15852step0 := by apply Matrix.ext; unfold raw15852step1 raw15852step0; decide +kernel
      have hl : raw15852step0Labels = labelEmbedding1 ∘ raw15852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15852step0 raw15852step0Labels raw15852step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw15853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw15853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15853step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15853step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15853 raw15853Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw15853 raw15853Labels = mixedMoment B raw15853step0 raw15853step0Labels := by
      have ha : raw15853step0 = (fun i j => raw15853 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15853step0 raw15853; decide +kernel
      have hl : raw15853step0Labels = raw15853Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15853 raw15853Labels permutation246 permutation5
    mixedMoment B raw15853step0 raw15853step0Labels = mixedMoment B raw15853step1 raw15853step1Labels := by
      have ha : raw15853step1 = -raw15853step0 := by apply Matrix.ext; change ∀ i j, raw15853step1 i j = -(raw15853step0 i j); unfold raw15853step1 raw15853step0; decide +kernel
      have hl : raw15853step1Labels = raw15853step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15853step1 raw15853step1Labels = mixedMoment B raw15853step2 raw15853step2Labels := by
      have ha : raw15853step2 = raw15853step1 := by apply Matrix.ext; unfold raw15853step2 raw15853step1; decide +kernel
      have hl : raw15853step1Labels = labelEmbedding1 ∘ raw15853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15853step1 raw15853step1Labels raw15853step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw15854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15854 raw15854Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw15854 raw15854Labels = mixedMoment B raw15854step0 raw15854step0Labels := by
      have ha : raw15854step0 = (fun i j => raw15854 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15854step0 raw15854; decide +kernel
      have hl : raw15854step0Labels = raw15854Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15854 raw15854Labels permutation668 permutation7
    mixedMoment B raw15854step0 raw15854step0Labels = mixedMoment B raw15854step1 raw15854step1Labels := by
      have ha : raw15854step1 = raw15854step0 := by apply Matrix.ext; unfold raw15854step1 raw15854step0; decide +kernel
      have hl : raw15854step0Labels = labelEmbedding1 ∘ raw15854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15854step0 raw15854step0Labels raw15854step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw15855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15855step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15855 raw15855Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw15855 raw15855Labels = mixedMoment B raw15855step0 raw15855step0Labels := by
      have ha : raw15855step0 = (fun i j => raw15855 (permutation669 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15855step0 raw15855; decide +kernel
      have hl : raw15855step0Labels = raw15855Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15855 raw15855Labels permutation669 permutation7
    mixedMoment B raw15855step0 raw15855step0Labels = mixedMoment B raw15855step1 raw15855step1Labels := by
      have ha : raw15855step1 = raw15855step0 := by apply Matrix.ext; unfold raw15855step1 raw15855step0; decide +kernel
      have hl : raw15855step0Labels = labelEmbedding1 ∘ raw15855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15855step0 raw15855step0Labels raw15855step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

def raw15856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw15856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15856 raw15856Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw15856 raw15856Labels = mixedMoment B raw15856step0 raw15856step0Labels := by
      have ha : raw15856step0 = (fun i j => raw15856 (permutation667 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15856step0 raw15856; decide +kernel
      have hl : raw15856step0Labels = raw15856Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15856 raw15856Labels permutation667 permutation7
    mixedMoment B raw15856step0 raw15856step0Labels = mixedMoment B raw15856step1 raw15856step1Labels := by
      have ha : raw15856step1 = raw15856step0 := by apply Matrix.ext; unfold raw15856step1 raw15856step0; decide +kernel
      have hl : raw15856step0Labels = labelEmbedding1 ∘ raw15856step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15856step0 raw15856step0Labels raw15856step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

def raw15857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw15857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15857 raw15857Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw15857 raw15857Labels = mixedMoment B raw15857step0 raw15857step0Labels := by
      have ha : raw15857step0 = (fun i j => raw15857 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15857step0 raw15857; decide +kernel
      have hl : raw15857step0Labels = raw15857Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15857 raw15857Labels permutation668 permutation7
    mixedMoment B raw15857step0 raw15857step0Labels = mixedMoment B raw15857step1 raw15857step1Labels := by
      have ha : raw15857step1 = raw15857step0 := by apply Matrix.ext; unfold raw15857step1 raw15857step0; decide +kernel
      have hl : raw15857step0Labels = labelEmbedding1 ∘ raw15857step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15857step0 raw15857step0Labels raw15857step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw15858 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15858step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15858step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15858 raw15858Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw15858 raw15858Labels = mixedMoment B raw15858step0 raw15858step0Labels := by
      have ha : raw15858step0 = (fun i j => raw15858 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15858step0 raw15858; decide +kernel
      have hl : raw15858step0Labels = raw15858Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15858 raw15858Labels permutation682 permutation7
    mixedMoment B raw15858step0 raw15858step0Labels = mixedMoment B raw15858step1 raw15858step1Labels := by
      have ha : raw15858step1 = -raw15858step0 := by apply Matrix.ext; change ∀ i j, raw15858step1 i j = -(raw15858step0 i j); unfold raw15858step1 raw15858step0; decide +kernel
      have hl : raw15858step1Labels = raw15858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15858step1 raw15858step1Labels = mixedMoment B raw15858step2 raw15858step2Labels := by
      have ha : raw15858step2 = raw15858step1 := by apply Matrix.ext; unfold raw15858step2 raw15858step1; decide +kernel
      have hl : raw15858step1Labels = labelEmbedding10 ∘ raw15858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15858step1 raw15858step1Labels raw15858step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw15859 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15859step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15859step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15859step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15859 raw15859Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw15859 raw15859Labels = mixedMoment B raw15859step0 raw15859step0Labels := by
      have hz : ∀ j, raw15859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15859step0 = (fun i j => raw15859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15859step0 raw15859; decide +kernel
      have hl : raw15859step0Labels = raw15859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15859 raw15859Labels permutation434 hz
    mixedMoment B raw15859step0 raw15859step0Labels = mixedMoment B raw15859step1 raw15859step1Labels := by
      have ha : raw15859step1 = (fun i j => raw15859step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15859step1 raw15859step0; decide +kernel
      have hl : raw15859step1Labels = raw15859step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15859step0 raw15859step0Labels permutation151 permutation7
    mixedMoment B raw15859step1 raw15859step1Labels = mixedMoment B raw15859step2 raw15859step2Labels := by
      have ha : raw15859step2 = -raw15859step1 := by apply Matrix.ext; change ∀ i j, raw15859step2 i j = -(raw15859step1 i j); unfold raw15859step2 raw15859step1; decide +kernel
      have hl : raw15859step2Labels = raw15859step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15859step2 raw15859step2Labels = mixedMoment B raw15859step3 raw15859step3Labels := by
      have ha : raw15859step3 = raw15859step2 := by apply Matrix.ext; unfold raw15859step3 raw15859step2; decide +kernel
      have hl : raw15859step2Labels = labelEmbedding10 ∘ raw15859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15859step2 raw15859step2Labels raw15859step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw15860 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15860 raw15860Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw15860 raw15860Labels = mixedMoment B raw15860step0 raw15860step0Labels := by
      have ha : raw15860step0 = (fun i j => raw15860 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15860step0 raw15860; decide +kernel
      have hl : raw15860step0Labels = raw15860Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15860 raw15860Labels permutation682 permutation2
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw15861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw15861step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw15861step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15861step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw15861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15861 raw15861Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw15861 raw15861Labels = mixedMoment B raw15861step0 raw15861step0Labels := by
      have ha : raw15861step0 = (fun i j => raw15861 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15861step0 raw15861; decide +kernel
      have hl : raw15861step0Labels = raw15861Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15861 raw15861Labels permutation240 permutation4
    mixedMoment B raw15861step0 raw15861step0Labels = mixedMoment B raw15861step1 raw15861step1Labels := by
      have ha : raw15861step1 = -raw15861step0 := by apply Matrix.ext; change ∀ i j, raw15861step1 i j = -(raw15861step0 i j); unfold raw15861step1 raw15861step0; decide +kernel
      have hl : raw15861step1Labels = raw15861step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15861step1 raw15861step1Labels = mixedMoment B raw15861step2 raw15861step2Labels := by
      have ha : raw15861step2 = raw15861step1 := by apply Matrix.ext; unfold raw15861step2 raw15861step1; decide +kernel
      have hl : raw15861step1Labels = labelEmbedding7 ∘ raw15861step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15861step1 raw15861step1Labels raw15861step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw15862 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15862step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15862step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15862step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15862step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15862 raw15862Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15862 raw15862Labels = mixedMoment B raw15862step0 raw15862step0Labels := by
      have hz : ∀ j, raw15862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15862step0 = (fun i j => raw15862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15862step0 raw15862; decide +kernel
      have hl : raw15862step0Labels = raw15862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15862 raw15862Labels permutation434 hz
    mixedMoment B raw15862step0 raw15862step0Labels = mixedMoment B raw15862step1 raw15862step1Labels := by
      have ha : raw15862step1 = (fun i j => raw15862step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15862step1 raw15862step0; decide +kernel
      have hl : raw15862step1Labels = raw15862step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15862step0 raw15862step0Labels permutation151 permutation7
    mixedMoment B raw15862step1 raw15862step1Labels = mixedMoment B raw15862step2 raw15862step2Labels := by
      have ha : raw15862step2 = -raw15862step1 := by apply Matrix.ext; change ∀ i j, raw15862step2 i j = -(raw15862step1 i j); unfold raw15862step2 raw15862step1; decide +kernel
      have hl : raw15862step2Labels = raw15862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15862step2 raw15862step2Labels = mixedMoment B raw15862step3 raw15862step3Labels := by
      have ha : raw15862step3 = raw15862step2 := by apply Matrix.ext; unfold raw15862step3 raw15862step2; decide +kernel
      have hl : raw15862step2Labels = labelEmbedding10 ∘ raw15862step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15862step2 raw15862step2Labels raw15862step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw15863 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15863 raw15863Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw15863 raw15863Labels = mixedMoment B raw15863step0 raw15863step0Labels := by
      have ha : raw15863step0 = (fun i j => raw15863 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15863step0 raw15863; decide +kernel
      have hl : raw15863step0Labels = raw15863Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15863 raw15863Labels permutation668 permutation2
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw15864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15864step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15864step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15864step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15864 raw15864Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw15864 raw15864Labels = mixedMoment B raw15864step0 raw15864step0Labels := by
      have ha : raw15864step0 = (fun i j => raw15864 (permutation169 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15864step0 raw15864; decide +kernel
      have hl : raw15864step0Labels = raw15864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15864 raw15864Labels permutation169 permutation4
    mixedMoment B raw15864step0 raw15864step0Labels = mixedMoment B raw15864step1 raw15864step1Labels := by
      have ha : raw15864step1 = -raw15864step0 := by apply Matrix.ext; change ∀ i j, raw15864step1 i j = -(raw15864step0 i j); unfold raw15864step1 raw15864step0; decide +kernel
      have hl : raw15864step1Labels = raw15864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15864step1 raw15864step1Labels = mixedMoment B raw15864step2 raw15864step2Labels := by
      have ha : raw15864step2 = raw15864step1 := by apply Matrix.ext; unfold raw15864step2 raw15864step1; decide +kernel
      have hl : raw15864step1Labels = labelEmbedding7 ∘ raw15864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15864step1 raw15864step1Labels raw15864step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw15865 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15865 raw15865Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw15865 raw15865Labels = mixedMoment B raw15865step0 raw15865step0Labels := by
      have ha : raw15865step0 = (fun i j => raw15865 (permutation672 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15865step0 raw15865; decide +kernel
      have hl : raw15865step0Labels = raw15865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15865 raw15865Labels permutation672 permutation2
    _ = mixedMoment B node5407 node5407Labels := by rfl

def raw15866 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15866 raw15866Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw15866 raw15866Labels = mixedMoment B raw15866step0 raw15866step0Labels := by
      have hz : ∀ j, raw15866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15866step0 = (fun i j => raw15866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15866step0 raw15866; decide +kernel
      have hl : raw15866step0Labels = raw15866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15866 raw15866Labels permutation434 hz
    mixedMoment B raw15866step0 raw15866step0Labels = mixedMoment B raw15866step1 raw15866step1Labels := by
      have ha : raw15866step1 = (fun i j => raw15866step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15866step1 raw15866step0; decide +kernel
      have hl : raw15866step1Labels = raw15866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15866step0 raw15866step0Labels permutation146 permutation2
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw15867 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15867 raw15867Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw15867 raw15867Labels = mixedMoment B raw15867step0 raw15867step0Labels := by
      have ha : raw15867step0 = (fun i j => raw15867 (permutation669 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15867step0 raw15867; decide +kernel
      have hl : raw15867step0Labels = raw15867Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15867 raw15867Labels permutation669 permutation2
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw15868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15868step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15868step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15868step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15868step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15868 raw15868Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw15868 raw15868Labels = mixedMoment B raw15868step0 raw15868step0Labels := by
      have ha : raw15868step0 = (fun i j => raw15868 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15868step0 raw15868; decide +kernel
      have hl : raw15868step0Labels = raw15868Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15868 raw15868Labels permutation168 permutation4
    mixedMoment B raw15868step0 raw15868step0Labels = mixedMoment B raw15868step1 raw15868step1Labels := by
      have ha : raw15868step1 = -raw15868step0 := by apply Matrix.ext; change ∀ i j, raw15868step1 i j = -(raw15868step0 i j); unfold raw15868step1 raw15868step0; decide +kernel
      have hl : raw15868step1Labels = raw15868step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15868step1 raw15868step1Labels = mixedMoment B raw15868step2 raw15868step2Labels := by
      have ha : raw15868step2 = raw15868step1 := by apply Matrix.ext; unfold raw15868step2 raw15868step1; decide +kernel
      have hl : raw15868step1Labels = labelEmbedding7 ∘ raw15868step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15868step1 raw15868step1Labels raw15868step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw15869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15869 raw15869Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw15869 raw15869Labels = mixedMoment B raw15869step0 raw15869step0Labels := by
      have ha : raw15869step0 = (fun i j => raw15869 (permutation671 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15869step0 raw15869; decide +kernel
      have hl : raw15869step0Labels = raw15869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15869 raw15869Labels permutation671 permutation2
    _ = mixedMoment B node5407 node5407Labels := by rfl

def raw15870 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15870 raw15870Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw15870 raw15870Labels = mixedMoment B raw15870step0 raw15870step0Labels := by
      have ha : raw15870step0 = (fun i j => raw15870 (permutation667 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15870step0 raw15870; decide +kernel
      have hl : raw15870step0Labels = raw15870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15870 raw15870Labels permutation667 permutation2
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw15871 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15871 raw15871Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw15871 raw15871Labels = mixedMoment B raw15871step0 raw15871step0Labels := by
      have ha : raw15871step0 = (fun i j => raw15871 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15871step0 raw15871; decide +kernel
      have hl : raw15871step0Labels = raw15871Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15871 raw15871Labels permutation152 permutation6
    _ = mixedMoment B node3977 node3977Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
