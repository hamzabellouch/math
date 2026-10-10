import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34688 raw34688Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw34688 raw34688Labels = mixedMoment B raw34688step0 raw34688step0Labels := by
      have hz : ∀ j, raw34688 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34688step0 = (fun i j => raw34688 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34688step0 raw34688; decide +kernel
      have hl : raw34688step0Labels = raw34688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34688 raw34688Labels permutation520 hz
    mixedMoment B raw34688step0 raw34688step0Labels = mixedMoment B raw34688step1 raw34688step1Labels := by
      have ha : raw34688step1 = (fun i j => raw34688step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34688step1 raw34688step0; decide +kernel
      have hl : raw34688step1Labels = raw34688step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34688step0 raw34688step0Labels permutation37 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw34689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34689 raw34689Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw34689 raw34689Labels = mixedMoment B raw34689step0 raw34689step0Labels := by
      have hz : ∀ j, raw34689 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34689step0 = (fun i j => raw34689 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34689step0 raw34689; decide +kernel
      have hl : raw34689step0Labels = raw34689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34689 raw34689Labels permutation590 hz
    mixedMoment B raw34689step0 raw34689step0Labels = mixedMoment B raw34689step1 raw34689step1Labels := by
      have ha : raw34689step1 = (fun i j => raw34689step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34689step1 raw34689step0; decide +kernel
      have hl : raw34689step1Labels = raw34689step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34689step0 raw34689step0Labels permutation37 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw34690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34690 raw34690Labels = mixedMoment B node4677 node4677Labels := by
  calc
    mixedMoment B raw34690 raw34690Labels = mixedMoment B raw34690step0 raw34690step0Labels := by
      have ha : raw34690step0 = (fun i j => raw34690 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34690step0 raw34690; decide +kernel
      have hl : raw34690step0Labels = raw34690Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34690 raw34690Labels permutation168 permutation2
    _ = mixedMoment B node4677 node4677Labels := by rfl

def raw34691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34691 raw34691Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw34691 raw34691Labels = mixedMoment B raw34691step0 raw34691step0Labels := by
      have ha : raw34691step0 = (fun i j => raw34691 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34691step0 raw34691; decide +kernel
      have hl : raw34691step0Labels = raw34691Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34691 raw34691Labels permutation155 permutation2
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw34692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34692 raw34692Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw34692 raw34692Labels = mixedMoment B raw34692step0 raw34692step0Labels := by
      have hz : ∀ j, raw34692 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34692step0 = (fun i j => raw34692 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34692step0 raw34692; decide +kernel
      have hl : raw34692step0Labels = raw34692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34692 raw34692Labels permutation520 hz
    mixedMoment B raw34692step0 raw34692step0Labels = mixedMoment B raw34692step1 raw34692step1Labels := by
      have ha : raw34692step1 = (fun i j => raw34692step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34692step1 raw34692step0; decide +kernel
      have hl : raw34692step1Labels = raw34692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34692step0 raw34692step0Labels permutation36 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw34693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34693 raw34693Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw34693 raw34693Labels = mixedMoment B raw34693step0 raw34693step0Labels := by
      have hz : ∀ j, raw34693 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34693step0 = (fun i j => raw34693 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34693step0 raw34693; decide +kernel
      have hl : raw34693step0Labels = raw34693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34693 raw34693Labels permutation590 hz
    mixedMoment B raw34693step0 raw34693step0Labels = mixedMoment B raw34693step1 raw34693step1Labels := by
      have ha : raw34693step1 = (fun i j => raw34693step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34693step1 raw34693step0; decide +kernel
      have hl : raw34693step1Labels = raw34693step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34693step0 raw34693step0Labels permutation36 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw34694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34694 raw34694Labels = mixedMoment B node4680 node4680Labels := by
  calc
    mixedMoment B raw34694 raw34694Labels = mixedMoment B raw34694step0 raw34694step0Labels := by
      have ha : raw34694step0 = (fun i j => raw34694 (permutation172 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34694step0 raw34694; decide +kernel
      have hl : raw34694step0Labels = raw34694Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34694 raw34694Labels permutation172 permutation2
    _ = mixedMoment B node4680 node4680Labels := by rfl

def raw34695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34695 raw34695Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw34695 raw34695Labels = mixedMoment B raw34695step0 raw34695step0Labels := by
      have ha : raw34695step0 = (fun i j => raw34695 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34695step0 raw34695; decide +kernel
      have hl : raw34695step0Labels = raw34695Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34695 raw34695Labels permutation156 permutation2
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw34696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34696 raw34696Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw34696 raw34696Labels = mixedMoment B raw34696step0 raw34696step0Labels := by
      have ha : raw34696step0 = (fun i j => raw34696 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34696step0 raw34696; decide +kernel
      have hl : raw34696step0Labels = raw34696Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34696 raw34696Labels permutation162 permutation2
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw34697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34697 raw34697Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw34697 raw34697Labels = mixedMoment B raw34697step0 raw34697step0Labels := by
      have hz : ∀ j, raw34697 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34697step0 = (fun i j => raw34697 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34697step0 raw34697; decide +kernel
      have hl : raw34697step0Labels = raw34697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34697 raw34697Labels permutation590 hz
    mixedMoment B raw34697step0 raw34697step0Labels = mixedMoment B raw34697step1 raw34697step1Labels := by
      have ha : raw34697step1 = (fun i j => raw34697step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34697step1 raw34697step0; decide +kernel
      have hl : raw34697step1Labels = raw34697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34697step0 raw34697step0Labels permutation34 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw34698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34698 raw34698Labels = mixedMoment B node4680 node4680Labels := by
  calc
    mixedMoment B raw34698 raw34698Labels = mixedMoment B raw34698step0 raw34698step0Labels := by
      have ha : raw34698step0 = (fun i j => raw34698 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34698step0 raw34698; decide +kernel
      have hl : raw34698step0Labels = raw34698Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34698 raw34698Labels permutation166 permutation2
    _ = mixedMoment B node4680 node4680Labels := by rfl

def raw34699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34699 raw34699Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw34699 raw34699Labels = mixedMoment B raw34699step0 raw34699step0Labels := by
      have ha : raw34699step0 = (fun i j => raw34699 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34699step0 raw34699; decide +kernel
      have hl : raw34699step0Labels = raw34699Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34699 raw34699Labels permutation154 permutation2
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw34700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34700 raw34700Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw34700 raw34700Labels = mixedMoment B raw34700step0 raw34700step0Labels := by
      have ha : raw34700step0 = (fun i j => raw34700 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34700step0 raw34700; decide +kernel
      have hl : raw34700step0Labels = raw34700Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34700 raw34700Labels permutation160 permutation2
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw34701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34701 raw34701Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw34701 raw34701Labels = mixedMoment B raw34701step0 raw34701step0Labels := by
      have hz : ∀ j, raw34701 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34701step0 = (fun i j => raw34701 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34701step0 raw34701; decide +kernel
      have hl : raw34701step0Labels = raw34701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34701 raw34701Labels permutation520 hz
    mixedMoment B raw34701step0 raw34701step0Labels = mixedMoment B raw34701step1 raw34701step1Labels := by
      have ha : raw34701step1 = (fun i j => raw34701step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34701step1 raw34701step0; decide +kernel
      have hl : raw34701step1Labels = raw34701step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34701step0 raw34701step0Labels permutation34 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw34702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34702step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34702 raw34702Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw34702 raw34702Labels = mixedMoment B raw34702step0 raw34702step0Labels := by
      have ha : raw34702step0 = (fun i j => raw34702 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34702step0 raw34702; decide +kernel
      have hl : raw34702step0Labels = raw34702Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34702 raw34702Labels permutation169 permutation7
    mixedMoment B raw34702step0 raw34702step0Labels = mixedMoment B raw34702step1 raw34702step1Labels := by
      have ha : raw34702step1 = -raw34702step0 := by apply Matrix.ext; change ∀ i j, raw34702step1 i j = -(raw34702step0 i j); unfold raw34702step1 raw34702step0; decide +kernel
      have hl : raw34702step1Labels = raw34702step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34702step1 raw34702step1Labels = mixedMoment B raw34702step2 raw34702step2Labels := by
      have ha : raw34702step2 = raw34702step1 := by apply Matrix.ext; unfold raw34702step2 raw34702step1; decide +kernel
      have hl : raw34702step1Labels = labelEmbedding1 ∘ raw34702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34702step1 raw34702step1Labels raw34702step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw34703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34703step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34703step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34703 raw34703Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw34703 raw34703Labels = mixedMoment B raw34703step0 raw34703step0Labels := by
      have ha : raw34703step0 = (fun i j => raw34703 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34703step0 raw34703; decide +kernel
      have hl : raw34703step0Labels = raw34703Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34703 raw34703Labels permutation169 permutation7
    mixedMoment B raw34703step0 raw34703step0Labels = mixedMoment B raw34703step1 raw34703step1Labels := by
      have ha : raw34703step1 = -raw34703step0 := by apply Matrix.ext; change ∀ i j, raw34703step1 i j = -(raw34703step0 i j); unfold raw34703step1 raw34703step0; decide +kernel
      have hl : raw34703step1Labels = raw34703step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34703step1 raw34703step1Labels = mixedMoment B raw34703step2 raw34703step2Labels := by
      have ha : raw34703step2 = raw34703step1 := by apply Matrix.ext; unfold raw34703step2 raw34703step1; decide +kernel
      have hl : raw34703step1Labels = labelEmbedding1 ∘ raw34703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34703step1 raw34703step1Labels raw34703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw34704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34704step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34704 raw34704Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw34704 raw34704Labels = mixedMoment B raw34704step0 raw34704step0Labels := by
      have ha : raw34704step0 = (fun i j => raw34704 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34704step0 raw34704; decide +kernel
      have hl : raw34704step0Labels = raw34704Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34704 raw34704Labels permutation169 permutation7
    mixedMoment B raw34704step0 raw34704step0Labels = mixedMoment B raw34704step1 raw34704step1Labels := by
      have ha : raw34704step1 = -raw34704step0 := by apply Matrix.ext; change ∀ i j, raw34704step1 i j = -(raw34704step0 i j); unfold raw34704step1 raw34704step0; decide +kernel
      have hl : raw34704step1Labels = raw34704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34704step1 raw34704step1Labels = mixedMoment B raw34704step2 raw34704step2Labels := by
      have ha : raw34704step2 = raw34704step1 := by apply Matrix.ext; unfold raw34704step2 raw34704step1; decide +kernel
      have hl : raw34704step1Labels = labelEmbedding1 ∘ raw34704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34704step1 raw34704step1Labels raw34704step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2709 node2709Labels := by rfl

def raw34705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34705step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34705step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34705step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34705 raw34705Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw34705 raw34705Labels = mixedMoment B raw34705step0 raw34705step0Labels := by
      have hz : ∀ j, raw34705 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34705step0 = (fun i j => raw34705 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34705step0 raw34705; decide +kernel
      have hl : raw34705step0Labels = raw34705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34705 raw34705Labels permutation520 hz
    mixedMoment B raw34705step0 raw34705step0Labels = mixedMoment B raw34705step1 raw34705step1Labels := by
      have ha : raw34705step1 = (fun i j => raw34705step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34705step1 raw34705step0; decide +kernel
      have hl : raw34705step1Labels = raw34705step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34705step0 raw34705step0Labels permutation37 permutation7
    mixedMoment B raw34705step1 raw34705step1Labels = mixedMoment B raw34705step2 raw34705step2Labels := by
      have ha : raw34705step2 = -raw34705step1 := by apply Matrix.ext; change ∀ i j, raw34705step2 i j = -(raw34705step1 i j); unfold raw34705step2 raw34705step1; decide +kernel
      have hl : raw34705step2Labels = raw34705step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34705step2 raw34705step2Labels = mixedMoment B raw34705step3 raw34705step3Labels := by
      have ha : raw34705step3 = raw34705step2 := by apply Matrix.ext; unfold raw34705step3 raw34705step2; decide +kernel
      have hl : raw34705step2Labels = labelEmbedding1 ∘ raw34705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34705step2 raw34705step2Labels raw34705step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw34706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34706step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34706 raw34706Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw34706 raw34706Labels = mixedMoment B raw34706step0 raw34706step0Labels := by
      have hz : ∀ j, raw34706 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34706step0 = (fun i j => raw34706 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34706step0 raw34706; decide +kernel
      have hl : raw34706step0Labels = raw34706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34706 raw34706Labels permutation590 hz
    mixedMoment B raw34706step0 raw34706step0Labels = mixedMoment B raw34706step1 raw34706step1Labels := by
      have ha : raw34706step1 = (fun i j => raw34706step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34706step1 raw34706step0; decide +kernel
      have hl : raw34706step1Labels = raw34706step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34706step0 raw34706step0Labels permutation37 permutation7
    mixedMoment B raw34706step1 raw34706step1Labels = mixedMoment B raw34706step2 raw34706step2Labels := by
      have ha : raw34706step2 = -raw34706step1 := by apply Matrix.ext; change ∀ i j, raw34706step2 i j = -(raw34706step1 i j); unfold raw34706step2 raw34706step1; decide +kernel
      have hl : raw34706step2Labels = raw34706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34706step2 raw34706step2Labels = mixedMoment B raw34706step3 raw34706step3Labels := by
      have ha : raw34706step3 = raw34706step2 := by apply Matrix.ext; unfold raw34706step3 raw34706step2; decide +kernel
      have hl : raw34706step2Labels = labelEmbedding1 ∘ raw34706step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34706step2 raw34706step2Labels raw34706step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw34707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34707 raw34707Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw34707 raw34707Labels = mixedMoment B raw34707step0 raw34707step0Labels := by
      have hz : ∀ j, raw34707 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34707step0 = (fun i j => raw34707 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34707step0 raw34707; decide +kernel
      have hl : raw34707step0Labels = raw34707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34707 raw34707Labels permutation265 hz
    mixedMoment B raw34707step0 raw34707step0Labels = mixedMoment B raw34707step1 raw34707step1Labels := by
      have ha : raw34707step1 = (fun i j => raw34707step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34707step1 raw34707step0; decide +kernel
      have hl : raw34707step1Labels = raw34707step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34707step0 raw34707step0Labels permutation49 permutation7
    mixedMoment B raw34707step1 raw34707step1Labels = mixedMoment B raw34707step2 raw34707step2Labels := by
      have ha : raw34707step2 = -raw34707step1 := by apply Matrix.ext; change ∀ i j, raw34707step2 i j = -(raw34707step1 i j); unfold raw34707step2 raw34707step1; decide +kernel
      have hl : raw34707step2Labels = raw34707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34707step2 raw34707step2Labels = mixedMoment B raw34707step3 raw34707step3Labels := by
      have ha : raw34707step3 = raw34707step2 := by apply Matrix.ext; unfold raw34707step3 raw34707step2; decide +kernel
      have hl : raw34707step2Labels = labelEmbedding1 ∘ raw34707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34707step2 raw34707step2Labels raw34707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw34708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34708step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34708step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34708 raw34708Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw34708 raw34708Labels = mixedMoment B raw34708step0 raw34708step0Labels := by
      have ha : raw34708step0 = (fun i j => raw34708 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34708step0 raw34708; decide +kernel
      have hl : raw34708step0Labels = raw34708Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34708 raw34708Labels permutation169 permutation7
    mixedMoment B raw34708step0 raw34708step0Labels = mixedMoment B raw34708step1 raw34708step1Labels := by
      have ha : raw34708step1 = -raw34708step0 := by apply Matrix.ext; change ∀ i j, raw34708step1 i j = -(raw34708step0 i j); unfold raw34708step1 raw34708step0; decide +kernel
      have hl : raw34708step1Labels = raw34708step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34708step1 raw34708step1Labels = mixedMoment B raw34708step2 raw34708step2Labels := by
      have ha : raw34708step2 = raw34708step1 := by apply Matrix.ext; unfold raw34708step2 raw34708step1; decide +kernel
      have hl : raw34708step1Labels = labelEmbedding1 ∘ raw34708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34708step1 raw34708step1Labels raw34708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

def raw34709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34709 raw34709Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw34709 raw34709Labels = mixedMoment B raw34709step0 raw34709step0Labels := by
      have ha : raw34709step0 = (fun i j => raw34709 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34709step0 raw34709; decide +kernel
      have hl : raw34709step0Labels = raw34709Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34709 raw34709Labels permutation169 permutation7
    mixedMoment B raw34709step0 raw34709step0Labels = mixedMoment B raw34709step1 raw34709step1Labels := by
      have ha : raw34709step1 = -raw34709step0 := by apply Matrix.ext; change ∀ i j, raw34709step1 i j = -(raw34709step0 i j); unfold raw34709step1 raw34709step0; decide +kernel
      have hl : raw34709step1Labels = raw34709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34709step1 raw34709step1Labels = mixedMoment B raw34709step2 raw34709step2Labels := by
      have ha : raw34709step2 = raw34709step1 := by apply Matrix.ext; unfold raw34709step2 raw34709step1; decide +kernel
      have hl : raw34709step1Labels = labelEmbedding1 ∘ raw34709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34709step1 raw34709step1Labels raw34709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw34710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34710 raw34710Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34710 raw34710Labels = mixedMoment B raw34710step0 raw34710step0Labels := by
      have hz : ∀ j, raw34710 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34710step0 = (fun i j => raw34710 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34710step0 raw34710; decide +kernel
      have hl : raw34710step0Labels = raw34710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34710 raw34710Labels permutation520 hz
    mixedMoment B raw34710step0 raw34710step0Labels = mixedMoment B raw34710step1 raw34710step1Labels := by
      have ha : raw34710step1 = (fun i j => raw34710step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34710step1 raw34710step0; decide +kernel
      have hl : raw34710step1Labels = raw34710step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34710step0 raw34710step0Labels permutation37 permutation7
    mixedMoment B raw34710step1 raw34710step1Labels = mixedMoment B raw34710step2 raw34710step2Labels := by
      have ha : raw34710step2 = -raw34710step1 := by apply Matrix.ext; change ∀ i j, raw34710step2 i j = -(raw34710step1 i j); unfold raw34710step2 raw34710step1; decide +kernel
      have hl : raw34710step2Labels = raw34710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34710step2 raw34710step2Labels = mixedMoment B raw34710step3 raw34710step3Labels := by
      have ha : raw34710step3 = raw34710step2 := by apply Matrix.ext; unfold raw34710step3 raw34710step2; decide +kernel
      have hl : raw34710step2Labels = labelEmbedding1 ∘ raw34710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34710step2 raw34710step2Labels raw34710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw34711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34711 raw34711Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34711 raw34711Labels = mixedMoment B raw34711step0 raw34711step0Labels := by
      have hz : ∀ j, raw34711 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34711step0 = (fun i j => raw34711 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34711step0 raw34711; decide +kernel
      have hl : raw34711step0Labels = raw34711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34711 raw34711Labels permutation590 hz
    mixedMoment B raw34711step0 raw34711step0Labels = mixedMoment B raw34711step1 raw34711step1Labels := by
      have ha : raw34711step1 = (fun i j => raw34711step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34711step1 raw34711step0; decide +kernel
      have hl : raw34711step1Labels = raw34711step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34711step0 raw34711step0Labels permutation37 permutation7
    mixedMoment B raw34711step1 raw34711step1Labels = mixedMoment B raw34711step2 raw34711step2Labels := by
      have ha : raw34711step2 = -raw34711step1 := by apply Matrix.ext; change ∀ i j, raw34711step2 i j = -(raw34711step1 i j); unfold raw34711step2 raw34711step1; decide +kernel
      have hl : raw34711step2Labels = raw34711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34711step2 raw34711step2Labels = mixedMoment B raw34711step3 raw34711step3Labels := by
      have ha : raw34711step3 = raw34711step2 := by apply Matrix.ext; unfold raw34711step3 raw34711step2; decide +kernel
      have hl : raw34711step2Labels = labelEmbedding1 ∘ raw34711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34711step2 raw34711step2Labels raw34711step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw34712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34712step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34712step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34712 raw34712Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw34712 raw34712Labels = mixedMoment B raw34712step0 raw34712step0Labels := by
      have ha : raw34712step0 = (fun i j => raw34712 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34712step0 raw34712; decide +kernel
      have hl : raw34712step0Labels = raw34712Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34712 raw34712Labels permutation169 permutation7
    mixedMoment B raw34712step0 raw34712step0Labels = mixedMoment B raw34712step1 raw34712step1Labels := by
      have ha : raw34712step1 = -raw34712step0 := by apply Matrix.ext; change ∀ i j, raw34712step1 i j = -(raw34712step0 i j); unfold raw34712step1 raw34712step0; decide +kernel
      have hl : raw34712step1Labels = raw34712step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34712step1 raw34712step1Labels = mixedMoment B raw34712step2 raw34712step2Labels := by
      have ha : raw34712step2 = raw34712step1 := by apply Matrix.ext; unfold raw34712step2 raw34712step1; decide +kernel
      have hl : raw34712step1Labels = labelEmbedding1 ∘ raw34712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34712step1 raw34712step1Labels raw34712step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

def raw34713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34713 raw34713Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw34713 raw34713Labels = mixedMoment B raw34713step0 raw34713step0Labels := by
      have ha : raw34713step0 = (fun i j => raw34713 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34713step0 raw34713; decide +kernel
      have hl : raw34713step0Labels = raw34713Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34713 raw34713Labels permutation169 permutation7
    mixedMoment B raw34713step0 raw34713step0Labels = mixedMoment B raw34713step1 raw34713step1Labels := by
      have ha : raw34713step1 = -raw34713step0 := by apply Matrix.ext; change ∀ i j, raw34713step1 i j = -(raw34713step0 i j); unfold raw34713step1 raw34713step0; decide +kernel
      have hl : raw34713step1Labels = raw34713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34713step1 raw34713step1Labels = mixedMoment B raw34713step2 raw34713step2Labels := by
      have ha : raw34713step2 = raw34713step1 := by apply Matrix.ext; unfold raw34713step2 raw34713step1; decide +kernel
      have hl : raw34713step1Labels = labelEmbedding1 ∘ raw34713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34713step1 raw34713step1Labels raw34713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw34714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34714 raw34714Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw34714 raw34714Labels = mixedMoment B raw34714step0 raw34714step0Labels := by
      have hz : ∀ j, raw34714 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34714step0 = (fun i j => raw34714 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34714step0 raw34714; decide +kernel
      have hl : raw34714step0Labels = raw34714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34714 raw34714Labels permutation520 hz
    mixedMoment B raw34714step0 raw34714step0Labels = mixedMoment B raw34714step1 raw34714step1Labels := by
      have ha : raw34714step1 = (fun i j => raw34714step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34714step1 raw34714step0; decide +kernel
      have hl : raw34714step1Labels = raw34714step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34714step0 raw34714step0Labels permutation37 permutation7
    mixedMoment B raw34714step1 raw34714step1Labels = mixedMoment B raw34714step2 raw34714step2Labels := by
      have ha : raw34714step2 = -raw34714step1 := by apply Matrix.ext; change ∀ i j, raw34714step2 i j = -(raw34714step1 i j); unfold raw34714step2 raw34714step1; decide +kernel
      have hl : raw34714step2Labels = raw34714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34714step2 raw34714step2Labels = mixedMoment B raw34714step3 raw34714step3Labels := by
      have ha : raw34714step3 = raw34714step2 := by apply Matrix.ext; unfold raw34714step3 raw34714step2; decide +kernel
      have hl : raw34714step2Labels = labelEmbedding1 ∘ raw34714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34714step2 raw34714step2Labels raw34714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw34715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34715step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34715 raw34715Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw34715 raw34715Labels = mixedMoment B raw34715step0 raw34715step0Labels := by
      have hz : ∀ j, raw34715 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34715step0 = (fun i j => raw34715 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34715step0 raw34715; decide +kernel
      have hl : raw34715step0Labels = raw34715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34715 raw34715Labels permutation590 hz
    mixedMoment B raw34715step0 raw34715step0Labels = mixedMoment B raw34715step1 raw34715step1Labels := by
      have ha : raw34715step1 = (fun i j => raw34715step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34715step1 raw34715step0; decide +kernel
      have hl : raw34715step1Labels = raw34715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34715step0 raw34715step0Labels permutation37 permutation7
    mixedMoment B raw34715step1 raw34715step1Labels = mixedMoment B raw34715step2 raw34715step2Labels := by
      have ha : raw34715step2 = -raw34715step1 := by apply Matrix.ext; change ∀ i j, raw34715step2 i j = -(raw34715step1 i j); unfold raw34715step2 raw34715step1; decide +kernel
      have hl : raw34715step2Labels = raw34715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34715step2 raw34715step2Labels = mixedMoment B raw34715step3 raw34715step3Labels := by
      have ha : raw34715step3 = raw34715step2 := by apply Matrix.ext; unfold raw34715step3 raw34715step2; decide +kernel
      have hl : raw34715step2Labels = labelEmbedding1 ∘ raw34715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34715step2 raw34715step2Labels raw34715step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw34716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34716 raw34716Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw34716 raw34716Labels = mixedMoment B raw34716step0 raw34716step0Labels := by
      have ha : raw34716step0 = (fun i j => raw34716 (permutation175 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34716step0 raw34716; decide +kernel
      have hl : raw34716step0Labels = raw34716Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34716 raw34716Labels permutation175 permutation7
    mixedMoment B raw34716step0 raw34716step0Labels = mixedMoment B raw34716step1 raw34716step1Labels := by
      have ha : raw34716step1 = -raw34716step0 := by apply Matrix.ext; change ∀ i j, raw34716step1 i j = -(raw34716step0 i j); unfold raw34716step1 raw34716step0; decide +kernel
      have hl : raw34716step1Labels = raw34716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34716step1 raw34716step1Labels = mixedMoment B raw34716step2 raw34716step2Labels := by
      have ha : raw34716step2 = raw34716step1 := by apply Matrix.ext; unfold raw34716step2 raw34716step1; decide +kernel
      have hl : raw34716step1Labels = labelEmbedding1 ∘ raw34716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34716step1 raw34716step1Labels raw34716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

def raw34717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34717step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34717step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34717 raw34717Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw34717 raw34717Labels = mixedMoment B raw34717step0 raw34717step0Labels := by
      have ha : raw34717step0 = (fun i j => raw34717 (permutation175 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34717step0 raw34717; decide +kernel
      have hl : raw34717step0Labels = raw34717Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34717 raw34717Labels permutation175 permutation7
    mixedMoment B raw34717step0 raw34717step0Labels = mixedMoment B raw34717step1 raw34717step1Labels := by
      have ha : raw34717step1 = -raw34717step0 := by apply Matrix.ext; change ∀ i j, raw34717step1 i j = -(raw34717step0 i j); unfold raw34717step1 raw34717step0; decide +kernel
      have hl : raw34717step1Labels = raw34717step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34717step1 raw34717step1Labels = mixedMoment B raw34717step2 raw34717step2Labels := by
      have ha : raw34717step2 = raw34717step1 := by apply Matrix.ext; unfold raw34717step2 raw34717step1; decide +kernel
      have hl : raw34717step1Labels = labelEmbedding1 ∘ raw34717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34717step1 raw34717step1Labels raw34717step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw34718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34718step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34718 raw34718Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw34718 raw34718Labels = mixedMoment B raw34718step0 raw34718step0Labels := by
      have ha : raw34718step0 = (fun i j => raw34718 (permutation175 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34718step0 raw34718; decide +kernel
      have hl : raw34718step0Labels = raw34718Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34718 raw34718Labels permutation175 permutation7
    mixedMoment B raw34718step0 raw34718step0Labels = mixedMoment B raw34718step1 raw34718step1Labels := by
      have ha : raw34718step1 = -raw34718step0 := by apply Matrix.ext; change ∀ i j, raw34718step1 i j = -(raw34718step0 i j); unfold raw34718step1 raw34718step0; decide +kernel
      have hl : raw34718step1Labels = raw34718step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34718step1 raw34718step1Labels = mixedMoment B raw34718step2 raw34718step2Labels := by
      have ha : raw34718step2 = raw34718step1 := by apply Matrix.ext; unfold raw34718step2 raw34718step1; decide +kernel
      have hl : raw34718step1Labels = labelEmbedding1 ∘ raw34718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34718step1 raw34718step1Labels raw34718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw34719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34719 raw34719Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw34719 raw34719Labels = mixedMoment B raw34719step0 raw34719step0Labels := by
      have hz : ∀ j, raw34719 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34719step0 = (fun i j => raw34719 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34719step0 raw34719; decide +kernel
      have hl : raw34719step0Labels = raw34719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34719 raw34719Labels permutation590 hz
    mixedMoment B raw34719step0 raw34719step0Labels = mixedMoment B raw34719step1 raw34719step1Labels := by
      have ha : raw34719step1 = (fun i j => raw34719step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34719step1 raw34719step0; decide +kernel
      have hl : raw34719step1Labels = raw34719step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34719step0 raw34719step0Labels permutation37 permutation7
    mixedMoment B raw34719step1 raw34719step1Labels = mixedMoment B raw34719step2 raw34719step2Labels := by
      have ha : raw34719step2 = -raw34719step1 := by apply Matrix.ext; change ∀ i j, raw34719step2 i j = -(raw34719step1 i j); unfold raw34719step2 raw34719step1; decide +kernel
      have hl : raw34719step2Labels = raw34719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34719step2 raw34719step2Labels = mixedMoment B raw34719step3 raw34719step3Labels := by
      have ha : raw34719step3 = raw34719step2 := by apply Matrix.ext; unfold raw34719step3 raw34719step2; decide +kernel
      have hl : raw34719step2Labels = labelEmbedding1 ∘ raw34719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34719step2 raw34719step2Labels raw34719step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw34720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34720step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34720step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34720 raw34720Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw34720 raw34720Labels = mixedMoment B raw34720step0 raw34720step0Labels := by
      have ha : raw34720step0 = (fun i j => raw34720 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34720step0 raw34720; decide +kernel
      have hl : raw34720step0Labels = raw34720Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34720 raw34720Labels permutation169 permutation7
    mixedMoment B raw34720step0 raw34720step0Labels = mixedMoment B raw34720step1 raw34720step1Labels := by
      have ha : raw34720step1 = -raw34720step0 := by apply Matrix.ext; change ∀ i j, raw34720step1 i j = -(raw34720step0 i j); unfold raw34720step1 raw34720step0; decide +kernel
      have hl : raw34720step1Labels = raw34720step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34720step1 raw34720step1Labels = mixedMoment B raw34720step2 raw34720step2Labels := by
      have ha : raw34720step2 = raw34720step1 := by apply Matrix.ext; unfold raw34720step2 raw34720step1; decide +kernel
      have hl : raw34720step1Labels = labelEmbedding1 ∘ raw34720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34720step1 raw34720step1Labels raw34720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

def raw34721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34721 raw34721Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw34721 raw34721Labels = mixedMoment B raw34721step0 raw34721step0Labels := by
      have ha : raw34721step0 = (fun i j => raw34721 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34721step0 raw34721; decide +kernel
      have hl : raw34721step0Labels = raw34721Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34721 raw34721Labels permutation169 permutation7
    mixedMoment B raw34721step0 raw34721step0Labels = mixedMoment B raw34721step1 raw34721step1Labels := by
      have ha : raw34721step1 = -raw34721step0 := by apply Matrix.ext; change ∀ i j, raw34721step1 i j = -(raw34721step0 i j); unfold raw34721step1 raw34721step0; decide +kernel
      have hl : raw34721step1Labels = raw34721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34721step1 raw34721step1Labels = mixedMoment B raw34721step2 raw34721step2Labels := by
      have ha : raw34721step2 = raw34721step1 := by apply Matrix.ext; unfold raw34721step2 raw34721step1; decide +kernel
      have hl : raw34721step1Labels = labelEmbedding1 ∘ raw34721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34721step1 raw34721step1Labels raw34721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw34722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34722step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34722 raw34722Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw34722 raw34722Labels = mixedMoment B raw34722step0 raw34722step0Labels := by
      have ha : raw34722step0 = (fun i j => raw34722 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34722step0 raw34722; decide +kernel
      have hl : raw34722step0Labels = raw34722Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34722 raw34722Labels permutation169 permutation7
    mixedMoment B raw34722step0 raw34722step0Labels = mixedMoment B raw34722step1 raw34722step1Labels := by
      have ha : raw34722step1 = -raw34722step0 := by apply Matrix.ext; change ∀ i j, raw34722step1 i j = -(raw34722step0 i j); unfold raw34722step1 raw34722step0; decide +kernel
      have hl : raw34722step1Labels = raw34722step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34722step1 raw34722step1Labels = mixedMoment B raw34722step2 raw34722step2Labels := by
      have ha : raw34722step2 = raw34722step1 := by apply Matrix.ext; unfold raw34722step2 raw34722step1; decide +kernel
      have hl : raw34722step1Labels = labelEmbedding1 ∘ raw34722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34722step1 raw34722step1Labels raw34722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw34723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34723 raw34723Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw34723 raw34723Labels = mixedMoment B raw34723step0 raw34723step0Labels := by
      have hz : ∀ j, raw34723 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34723step0 = (fun i j => raw34723 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34723step0 raw34723; decide +kernel
      have hl : raw34723step0Labels = raw34723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34723 raw34723Labels permutation520 hz
    mixedMoment B raw34723step0 raw34723step0Labels = mixedMoment B raw34723step1 raw34723step1Labels := by
      have ha : raw34723step1 = (fun i j => raw34723step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34723step1 raw34723step0; decide +kernel
      have hl : raw34723step1Labels = raw34723step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34723step0 raw34723step0Labels permutation37 permutation7
    mixedMoment B raw34723step1 raw34723step1Labels = mixedMoment B raw34723step2 raw34723step2Labels := by
      have ha : raw34723step2 = -raw34723step1 := by apply Matrix.ext; change ∀ i j, raw34723step2 i j = -(raw34723step1 i j); unfold raw34723step2 raw34723step1; decide +kernel
      have hl : raw34723step2Labels = raw34723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34723step2 raw34723step2Labels = mixedMoment B raw34723step3 raw34723step3Labels := by
      have ha : raw34723step3 = raw34723step2 := by apply Matrix.ext; unfold raw34723step3 raw34723step2; decide +kernel
      have hl : raw34723step2Labels = labelEmbedding1 ∘ raw34723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34723step2 raw34723step2Labels raw34723step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw34724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34724step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]
def raw34724step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34724step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34724step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34724 raw34724Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw34724 raw34724Labels = mixedMoment B raw34724step0 raw34724step0Labels := by
      have hz : ∀ i, raw34724 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34724step0 = (fun i j => raw34724 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34724step0 raw34724; decide +kernel
      have hl : raw34724step0Labels = (fun j => raw34724Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34724 raw34724Labels permutation6 hz
    mixedMoment B raw34724step0 raw34724step0Labels = mixedMoment B raw34724step1 raw34724step1Labels := by
      have ha : raw34724step1 = (fun i j => raw34724step0 (permutation161 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34724step1 raw34724step0; decide +kernel
      have hl : raw34724step1Labels = raw34724step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34724step0 raw34724step0Labels permutation161 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

def raw34725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34725step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34725step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw34725step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34725step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34725step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34725 raw34725Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34725 raw34725Labels = mixedMoment B raw34725step0 raw34725step0Labels := by
      have hz : ∀ j, raw34725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34725step0 = (fun i j => raw34725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34725step0 raw34725; decide +kernel
      have hl : raw34725step0Labels = raw34725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34725 raw34725Labels permutation434 hz
    mixedMoment B raw34725step0 raw34725step0Labels = mixedMoment B raw34725step1 raw34725step1Labels := by
      have hz : ∀ i, raw34725step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34725step1 = (fun i j => raw34725step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34725step1 raw34725step0; decide +kernel
      have hl : raw34725step1Labels = (fun j => raw34725step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34725step0 raw34725step0Labels permutation6 hz
    mixedMoment B raw34725step1 raw34725step1Labels = mixedMoment B raw34725step2 raw34725step2Labels := by
      have ha : raw34725step2 = (fun i j => raw34725step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34725step2 raw34725step1; decide +kernel
      have hl : raw34725step2Labels = raw34725step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34725step1 raw34725step1Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw34726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw34726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34726step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34726step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw34726step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34726step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34726step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34726 raw34726Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34726 raw34726Labels = mixedMoment B raw34726step0 raw34726step0Labels := by
      have hz : ∀ j, raw34726 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34726step0 = (fun i j => raw34726 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34726step0 raw34726; decide +kernel
      have hl : raw34726step0Labels = raw34726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34726 raw34726Labels permutation520 hz
    mixedMoment B raw34726step0 raw34726step0Labels = mixedMoment B raw34726step1 raw34726step1Labels := by
      have hz : ∀ i, raw34726step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34726step1 = (fun i j => raw34726step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34726step1 raw34726step0; decide +kernel
      have hl : raw34726step1Labels = (fun j => raw34726step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34726step0 raw34726step0Labels permutation6 hz
    mixedMoment B raw34726step1 raw34726step1Labels = mixedMoment B raw34726step2 raw34726step2Labels := by
      have ha : raw34726step2 = (fun i j => raw34726step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34726step2 raw34726step1; decide +kernel
      have hl : raw34726step2Labels = raw34726step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34726step1 raw34726step1Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw34727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw34727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34727step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw34727step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34727step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34727step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34727 raw34727Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34727 raw34727Labels = mixedMoment B raw34727step0 raw34727step0Labels := by
      have hz : ∀ j, raw34727 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34727step0 = (fun i j => raw34727 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34727step0 raw34727; decide +kernel
      have hl : raw34727step0Labels = raw34727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34727 raw34727Labels permutation590 hz
    mixedMoment B raw34727step0 raw34727step0Labels = mixedMoment B raw34727step1 raw34727step1Labels := by
      have hz : ∀ i, raw34727step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34727step1 = (fun i j => raw34727step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34727step1 raw34727step0; decide +kernel
      have hl : raw34727step1Labels = (fun j => raw34727step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34727step0 raw34727step0Labels permutation6 hz
    mixedMoment B raw34727step1 raw34727step1Labels = mixedMoment B raw34727step2 raw34727step2Labels := by
      have ha : raw34727step2 = (fun i j => raw34727step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34727step2 raw34727step1; decide +kernel
      have hl : raw34727step2Labels = raw34727step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34727step1 raw34727step1Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw34728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34728step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]
def raw34728step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34728step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34728step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34728 raw34728Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw34728 raw34728Labels = mixedMoment B raw34728step0 raw34728step0Labels := by
      have hz : ∀ i, raw34728 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34728step0 = (fun i j => raw34728 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34728step0 raw34728; decide +kernel
      have hl : raw34728step0Labels = (fun j => raw34728Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34728 raw34728Labels permutation6 hz
    mixedMoment B raw34728step0 raw34728step0Labels = mixedMoment B raw34728step1 raw34728step1Labels := by
      have ha : raw34728step1 = (fun i j => raw34728step0 (permutation155 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34728step1 raw34728step0; decide +kernel
      have hl : raw34728step1Labels = raw34728step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34728step0 raw34728step0Labels permutation155 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

def raw34729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw34729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw34729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34729step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw34729step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34729step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34729step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34729 raw34729Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34729 raw34729Labels = mixedMoment B raw34729step0 raw34729step0Labels := by
      have hz : ∀ j, raw34729 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34729step0 = (fun i j => raw34729 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34729step0 raw34729; decide +kernel
      have hl : raw34729step0Labels = raw34729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34729 raw34729Labels permutation520 hz
    mixedMoment B raw34729step0 raw34729step0Labels = mixedMoment B raw34729step1 raw34729step1Labels := by
      have hz : ∀ i, raw34729step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34729step1 = (fun i j => raw34729step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34729step1 raw34729step0; decide +kernel
      have hl : raw34729step1Labels = (fun j => raw34729step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34729step0 raw34729step0Labels permutation6 hz
    mixedMoment B raw34729step1 raw34729step1Labels = mixedMoment B raw34729step2 raw34729step2Labels := by
      have ha : raw34729step2 = (fun i j => raw34729step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34729step2 raw34729step1; decide +kernel
      have hl : raw34729step2Labels = raw34729step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34729step1 raw34729step1Labels permutation33 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw34730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw34730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw34730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34730step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw34730step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34730step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34730step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34730 raw34730Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34730 raw34730Labels = mixedMoment B raw34730step0 raw34730step0Labels := by
      have hz : ∀ j, raw34730 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34730step0 = (fun i j => raw34730 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34730step0 raw34730; decide +kernel
      have hl : raw34730step0Labels = raw34730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34730 raw34730Labels permutation590 hz
    mixedMoment B raw34730step0 raw34730step0Labels = mixedMoment B raw34730step1 raw34730step1Labels := by
      have hz : ∀ i, raw34730step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34730step1 = (fun i j => raw34730step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34730step1 raw34730step0; decide +kernel
      have hl : raw34730step1Labels = (fun j => raw34730step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34730step0 raw34730step0Labels permutation6 hz
    mixedMoment B raw34730step1 raw34730step1Labels = mixedMoment B raw34730step2 raw34730step2Labels := by
      have ha : raw34730step2 = (fun i j => raw34730step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34730step2 raw34730step1; decide +kernel
      have hl : raw34730step2Labels = raw34730step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34730step1 raw34730step1Labels permutation33 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw34731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw34731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34731step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]
def raw34731step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34731step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34731step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34731 raw34731Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw34731 raw34731Labels = mixedMoment B raw34731step0 raw34731step0Labels := by
      have hz : ∀ i, raw34731 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34731step0 = (fun i j => raw34731 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34731step0 raw34731; decide +kernel
      have hl : raw34731step0Labels = (fun j => raw34731Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34731 raw34731Labels permutation6 hz
    mixedMoment B raw34731step0 raw34731step0Labels = mixedMoment B raw34731step1 raw34731step1Labels := by
      have ha : raw34731step1 = (fun i j => raw34731step0 (permutation153 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34731step1 raw34731step0; decide +kernel
      have hl : raw34731step1Labels = raw34731step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34731step0 raw34731step0Labels permutation153 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

def raw34732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw34732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34732step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34732step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34732 raw34732Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34732 raw34732Labels = mixedMoment B raw34732step0 raw34732step0Labels := by
      have hz : ∀ j, raw34732 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34732step0 = (fun i j => raw34732 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34732step0 raw34732; decide +kernel
      have hl : raw34732step0Labels = raw34732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34732 raw34732Labels permutation590 hz
    mixedMoment B raw34732step0 raw34732step0Labels = mixedMoment B raw34732step1 raw34732step1Labels := by
      have hz : ∀ i, raw34732step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34732step1 = (fun i j => raw34732step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34732step1 raw34732step0; decide +kernel
      have hl : raw34732step1Labels = (fun j => raw34732step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34732step0 raw34732step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw34733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34733 raw34733Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw34733 raw34733Labels = mixedMoment B raw34733step0 raw34733step0Labels := by
      have hz : ∀ j, raw34733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34733step0 = (fun i j => raw34733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34733step0 raw34733; decide +kernel
      have hl : raw34733step0Labels = raw34733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34733 raw34733Labels permutation346 hz
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw34734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-3, 3, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34734 raw34734Labels = mixedMoment B node3131 node3131Labels := by
  calc
    mixedMoment B raw34734 raw34734Labels = mixedMoment B raw34734step0 raw34734step0Labels := by
      have hz : ∀ j, raw34734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34734step0 = (fun i j => raw34734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34734step0 raw34734; decide +kernel
      have hl : raw34734step0Labels = raw34734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34734 raw34734Labels permutation346 hz
    mixedMoment B raw34734step0 raw34734step0Labels = mixedMoment B raw34734step1 raw34734step1Labels := by
      have ha : raw34734step1 = (fun i j => raw34734step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34734step1 raw34734step0; decide +kernel
      have hl : raw34734step1Labels = raw34734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34734step0 raw34734step0Labels permutation56 permutation2
    _ = mixedMoment B node3131 node3131Labels := by rfl

def raw34735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34735 raw34735Labels = mixedMoment B node3365 node3365Labels := by
  calc
    _ = mixedMoment B node3365 node3365Labels := by rfl

def raw34736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34736 raw34736Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw34736 raw34736Labels = mixedMoment B raw34736step0 raw34736step0Labels := by
      have hz : ∀ j, raw34736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34736step0 = (fun i j => raw34736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34736step0 raw34736; decide +kernel
      have hl : raw34736step0Labels = raw34736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34736 raw34736Labels permutation346 hz
    _ = mixedMoment B node3379 node3379Labels := by rfl

def raw34737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34737 raw34737Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw34737 raw34737Labels = mixedMoment B raw34737step0 raw34737step0Labels := by
      have hz : ∀ j, raw34737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34737step0 = (fun i j => raw34737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34737step0 raw34737; decide +kernel
      have hl : raw34737step0Labels = raw34737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34737 raw34737Labels permutation346 hz
    mixedMoment B raw34737step0 raw34737step0Labels = mixedMoment B raw34737step1 raw34737step1Labels := by
      have ha : raw34737step1 = (fun i j => raw34737step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34737step1 raw34737step0; decide +kernel
      have hl : raw34737step1Labels = raw34737step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34737step0 raw34737step0Labels permutation34 permutation2
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw34738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34738 raw34738Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw34738 raw34738Labels = mixedMoment B raw34738step0 raw34738step0Labels := by
      have hz : ∀ j, raw34738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34738step0 = (fun i j => raw34738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34738step0 raw34738; decide +kernel
      have hl : raw34738step0Labels = raw34738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34738 raw34738Labels permutation346 hz
    mixedMoment B raw34738step0 raw34738step0Labels = mixedMoment B raw34738step1 raw34738step1Labels := by
      have ha : raw34738step1 = (fun i j => raw34738step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34738step1 raw34738step0; decide +kernel
      have hl : raw34738step1Labels = raw34738step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34738step0 raw34738step0Labels permutation33 permutation2
    _ = mixedMoment B node3395 node3395Labels := by rfl

def raw34739 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]
def raw34739Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34739step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw34739step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34739step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw34739step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34739step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw34739step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34739 raw34739Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw34739 raw34739Labels = mixedMoment B raw34739step0 raw34739step0Labels := by
      have hz : ∀ j, raw34739 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34739step0 = (fun i j => raw34739 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34739step0 raw34739; decide +kernel
      have hl : raw34739step0Labels = raw34739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34739 raw34739Labels permutation520 hz
    mixedMoment B raw34739step0 raw34739step0Labels = mixedMoment B raw34739step1 raw34739step1Labels := by
      have hz : ∀ j, raw34739step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34739step1 = (fun i j => raw34739step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34739step1 raw34739step0; decide +kernel
      have hl : raw34739step1Labels = raw34739step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34739step0 raw34739step0Labels permutation80 hz
    mixedMoment B raw34739step1 raw34739step1Labels = mixedMoment B raw34739step2 raw34739step2Labels := by
      have hz : ∀ j, raw34739step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw34739step2 = (fun i j => raw34739step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw34739step2 raw34739step1; decide +kernel
      have hl : raw34739step2Labels = raw34739step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34739step1 raw34739step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw34740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34740 raw34740Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw34740 raw34740Labels = mixedMoment B raw34740step0 raw34740step0Labels := by
      have hz : ∀ j, raw34740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34740step0 = (fun i j => raw34740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34740step0 raw34740; decide +kernel
      have hl : raw34740step0Labels = raw34740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34740 raw34740Labels permutation346 hz
    mixedMoment B raw34740step0 raw34740step0Labels = mixedMoment B raw34740step1 raw34740step1Labels := by
      have ha : raw34740step1 = (fun i j => raw34740step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34740step1 raw34740step0; decide +kernel
      have hl : raw34740step1Labels = raw34740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34740step0 raw34740step0Labels permutation123 permutation2
    mixedMoment B raw34740step1 raw34740step1Labels = mixedMoment B raw34740step2 raw34740step2Labels := by
      have ha : raw34740step2 = -raw34740step1 := by apply Matrix.ext; change ∀ i j, raw34740step2 i j = -(raw34740step1 i j); unfold raw34740step2 raw34740step1; decide +kernel
      have hl : raw34740step2Labels = raw34740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw34741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34741 raw34741Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw34741 raw34741Labels = mixedMoment B raw34741step0 raw34741step0Labels := by
      have hz : ∀ j, raw34741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34741step0 = (fun i j => raw34741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34741step0 raw34741; decide +kernel
      have hl : raw34741step0Labels = raw34741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34741 raw34741Labels permutation346 hz
    mixedMoment B raw34741step0 raw34741step0Labels = mixedMoment B raw34741step1 raw34741step1Labels := by
      have ha : raw34741step1 = (fun i j => raw34741step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34741step1 raw34741step0; decide +kernel
      have hl : raw34741step1Labels = raw34741step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34741step0 raw34741step0Labels permutation46 permutation4
    mixedMoment B raw34741step1 raw34741step1Labels = mixedMoment B raw34741step2 raw34741step2Labels := by
      have ha : raw34741step2 = -raw34741step1 := by apply Matrix.ext; change ∀ i j, raw34741step2 i j = -(raw34741step1 i j); unfold raw34741step2 raw34741step1; decide +kernel
      have hl : raw34741step2Labels = raw34741step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw34742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw34742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw34742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34742 raw34742Labels = mixedMoment B node3032 node3032Labels := by
  calc
    mixedMoment B raw34742 raw34742Labels = mixedMoment B raw34742step0 raw34742step0Labels := by
      have ha : raw34742step0 = (fun i j => raw34742 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34742step0 raw34742; decide +kernel
      have hl : raw34742step0Labels = raw34742Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34742 raw34742Labels permutation234 permutation4
    mixedMoment B raw34742step0 raw34742step0Labels = mixedMoment B raw34742step1 raw34742step1Labels := by
      have ha : raw34742step1 = -raw34742step0 := by apply Matrix.ext; change ∀ i j, raw34742step1 i j = -(raw34742step0 i j); unfold raw34742step1 raw34742step0; decide +kernel
      have hl : raw34742step1Labels = raw34742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3032 node3032Labels := by rfl

def raw34743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw34743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34743 raw34743Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw34743 raw34743Labels = mixedMoment B raw34743step0 raw34743step0Labels := by
      have hz : ∀ j, raw34743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34743step0 = (fun i j => raw34743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34743step0 raw34743; decide +kernel
      have hl : raw34743step0Labels = raw34743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34743 raw34743Labels permutation346 hz
    mixedMoment B raw34743step0 raw34743step0Labels = mixedMoment B raw34743step1 raw34743step1Labels := by
      have ha : raw34743step1 = (fun i j => raw34743step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34743step1 raw34743step0; decide +kernel
      have hl : raw34743step1Labels = raw34743step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34743step0 raw34743step0Labels permutation44 permutation4
    mixedMoment B raw34743step1 raw34743step1Labels = mixedMoment B raw34743step2 raw34743step2Labels := by
      have ha : raw34743step2 = -raw34743step1 := by apply Matrix.ext; change ∀ i j, raw34743step2 i j = -(raw34743step1 i j); unfold raw34743step2 raw34743step1; decide +kernel
      have hl : raw34743step2Labels = raw34743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3045 node3045Labels := by rfl

def raw34744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw34744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -2, 0]]
def raw34744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw34744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw34744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34744 raw34744Labels = mixedMoment B node2362 node2362Labels := by
  calc
    mixedMoment B raw34744 raw34744Labels = mixedMoment B raw34744step0 raw34744step0Labels := by
      have hz : ∀ j, raw34744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34744step0 = (fun i j => raw34744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34744step0 raw34744; decide +kernel
      have hl : raw34744step0Labels = raw34744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34744 raw34744Labels permutation346 hz
    mixedMoment B raw34744step0 raw34744step0Labels = mixedMoment B raw34744step1 raw34744step1Labels := by
      have ha : raw34744step1 = (fun i j => raw34744step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34744step1 raw34744step0; decide +kernel
      have hl : raw34744step1Labels = raw34744step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34744step0 raw34744step0Labels permutation126 permutation2
    mixedMoment B raw34744step1 raw34744step1Labels = mixedMoment B raw34744step2 raw34744step2Labels := by
      have ha : raw34744step2 = -raw34744step1 := by apply Matrix.ext; change ∀ i j, raw34744step2 i j = -(raw34744step1 i j); unfold raw34744step2 raw34744step1; decide +kernel
      have hl : raw34744step2Labels = raw34744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2362 node2362Labels := by rfl

def raw34745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw34745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw34745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw34745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw34745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34745 raw34745Labels = mixedMoment B node3033 node3033Labels := by
  calc
    mixedMoment B raw34745 raw34745Labels = mixedMoment B raw34745step0 raw34745step0Labels := by
      have hz : ∀ j, raw34745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34745step0 = (fun i j => raw34745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34745step0 raw34745; decide +kernel
      have hl : raw34745step0Labels = raw34745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34745 raw34745Labels permutation346 hz
    mixedMoment B raw34745step0 raw34745step0Labels = mixedMoment B raw34745step1 raw34745step1Labels := by
      have ha : raw34745step1 = (fun i j => raw34745step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34745step1 raw34745step0; decide +kernel
      have hl : raw34745step1Labels = raw34745step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34745step0 raw34745step0Labels permutation46 permutation4
    mixedMoment B raw34745step1 raw34745step1Labels = mixedMoment B raw34745step2 raw34745step2Labels := by
      have ha : raw34745step2 = -raw34745step1 := by apply Matrix.ext; change ∀ i j, raw34745step2 i j = -(raw34745step1 i j); unfold raw34745step2 raw34745step1; decide +kernel
      have hl : raw34745step2Labels = raw34745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3033 node3033Labels := by rfl

def raw34746 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![0, 0]]
def raw34746Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34746step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![0, 0], ![-1, 1], ![2, -2]]
def raw34746step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34746step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![-1, 1], ![2, -2]]
def raw34746step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34746step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw34746step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34746 raw34746Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw34746 raw34746Labels = mixedMoment B raw34746step0 raw34746step0Labels := by
      have hz : ∀ j, raw34746 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34746step0 = (fun i j => raw34746 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34746step0 raw34746; decide +kernel
      have hl : raw34746step0Labels = raw34746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34746 raw34746Labels permutation590 hz
    mixedMoment B raw34746step0 raw34746step0Labels = mixedMoment B raw34746step1 raw34746step1Labels := by
      have hz : ∀ j, raw34746step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34746step1 = (fun i j => raw34746step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34746step1 raw34746step0; decide +kernel
      have hl : raw34746step1Labels = raw34746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34746step0 raw34746step0Labels permutation80 hz
    mixedMoment B raw34746step1 raw34746step1Labels = mixedMoment B raw34746step2 raw34746step2Labels := by
      have ha : raw34746step2 = (fun i j => raw34746step1 (permutation16 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34746step2 raw34746step1; decide +kernel
      have hl : raw34746step2Labels = raw34746step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34746step1 raw34746step1Labels permutation16 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw34747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34747 raw34747Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw34747 raw34747Labels = mixedMoment B raw34747step0 raw34747step0Labels := by
      have hz : ∀ j, raw34747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34747step0 = (fun i j => raw34747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34747step0 raw34747; decide +kernel
      have hl : raw34747step0Labels = raw34747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34747 raw34747Labels permutation346 hz
    _ = mixedMoment B node1815 node1815Labels := by rfl

def raw34748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-3, 3, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34748 raw34748Labels = mixedMoment B node3132 node3132Labels := by
  calc
    mixedMoment B raw34748 raw34748Labels = mixedMoment B raw34748step0 raw34748step0Labels := by
      have hz : ∀ j, raw34748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34748step0 = (fun i j => raw34748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34748step0 raw34748; decide +kernel
      have hl : raw34748step0Labels = raw34748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34748 raw34748Labels permutation346 hz
    mixedMoment B raw34748step0 raw34748step0Labels = mixedMoment B raw34748step1 raw34748step1Labels := by
      have ha : raw34748step1 = (fun i j => raw34748step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34748step1 raw34748step0; decide +kernel
      have hl : raw34748step1Labels = raw34748step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34748step0 raw34748step0Labels permutation56 permutation2
    _ = mixedMoment B node3132 node3132Labels := by rfl

def raw34749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34749 raw34749Labels = mixedMoment B node3366 node3366Labels := by
  calc
    _ = mixedMoment B node3366 node3366Labels := by rfl

def raw34750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34750 raw34750Labels = mixedMoment B node3380 node3380Labels := by
  calc
    mixedMoment B raw34750 raw34750Labels = mixedMoment B raw34750step0 raw34750step0Labels := by
      have hz : ∀ j, raw34750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34750step0 = (fun i j => raw34750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34750step0 raw34750; decide +kernel
      have hl : raw34750step0Labels = raw34750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34750 raw34750Labels permutation346 hz
    _ = mixedMoment B node3380 node3380Labels := by rfl

def raw34751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34751 raw34751Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw34751 raw34751Labels = mixedMoment B raw34751step0 raw34751step0Labels := by
      have hz : ∀ j, raw34751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34751step0 = (fun i j => raw34751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34751step0 raw34751; decide +kernel
      have hl : raw34751step0Labels = raw34751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34751 raw34751Labels permutation346 hz
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw34752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34752 raw34752Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw34752 raw34752Labels = mixedMoment B raw34752step0 raw34752step0Labels := by
      have hz : ∀ j, raw34752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34752step0 = (fun i j => raw34752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34752step0 raw34752; decide +kernel
      have hl : raw34752step0Labels = raw34752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34752 raw34752Labels permutation346 hz
    mixedMoment B raw34752step0 raw34752step0Labels = mixedMoment B raw34752step1 raw34752step1Labels := by
      have ha : raw34752step1 = (fun i j => raw34752step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34752step1 raw34752step0; decide +kernel
      have hl : raw34752step1Labels = raw34752step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34752step0 raw34752step0Labels permutation33 permutation2
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw34753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34753 raw34753Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw34753 raw34753Labels = mixedMoment B raw34753step0 raw34753step0Labels := by
      have hz : ∀ j, raw34753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34753step0 = (fun i j => raw34753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34753step0 raw34753; decide +kernel
      have hl : raw34753step0Labels = raw34753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34753 raw34753Labels permutation346 hz
    mixedMoment B raw34753step0 raw34753step0Labels = mixedMoment B raw34753step1 raw34753step1Labels := by
      have ha : raw34753step1 = (fun i j => raw34753step0 (permutation62 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34753step1 raw34753step0; decide +kernel
      have hl : raw34753step1Labels = raw34753step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34753step0 raw34753step0Labels permutation62 permutation2
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw34754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw34754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw34754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34754 raw34754Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw34754 raw34754Labels = mixedMoment B raw34754step0 raw34754step0Labels := by
      have hz : ∀ j, raw34754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34754step0 = (fun i j => raw34754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34754step0 raw34754; decide +kernel
      have hl : raw34754step0Labels = raw34754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34754 raw34754Labels permutation346 hz
    mixedMoment B raw34754step0 raw34754step0Labels = mixedMoment B raw34754step1 raw34754step1Labels := by
      have ha : raw34754step1 = (fun i j => raw34754step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34754step1 raw34754step0; decide +kernel
      have hl : raw34754step1Labels = raw34754step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34754step0 raw34754step0Labels permutation41 permutation4
    mixedMoment B raw34754step1 raw34754step1Labels = mixedMoment B raw34754step2 raw34754step2Labels := by
      have ha : raw34754step2 = -raw34754step1 := by apply Matrix.ext; change ∀ i j, raw34754step2 i j = -(raw34754step1 i j); unfold raw34754step2 raw34754step1; decide +kernel
      have hl : raw34754step2Labels = raw34754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3108 node3108Labels := by rfl

def raw34755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1], ![-1, 1, 0]]
def raw34755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, -1, 0]]
def raw34755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34755 raw34755Labels = mixedMoment B node3107 node3107Labels := by
  calc
    mixedMoment B raw34755 raw34755Labels = mixedMoment B raw34755step0 raw34755step0Labels := by
      have ha : raw34755step0 = (fun i j => raw34755 (permutation203 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34755step0 raw34755; decide +kernel
      have hl : raw34755step0Labels = raw34755Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34755 raw34755Labels permutation203 permutation4
    mixedMoment B raw34755step0 raw34755step0Labels = mixedMoment B raw34755step1 raw34755step1Labels := by
      have ha : raw34755step1 = -raw34755step0 := by apply Matrix.ext; change ∀ i j, raw34755step1 i j = -(raw34755step0 i j); unfold raw34755step1 raw34755step0; decide +kernel
      have hl : raw34755step1Labels = raw34755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3107 node3107Labels := by rfl

def raw34756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1], ![-1, 0, 1]]
def raw34756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw34756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34756 raw34756Labels = mixedMoment B node3115 node3115Labels := by
  calc
    mixedMoment B raw34756 raw34756Labels = mixedMoment B raw34756step0 raw34756step0Labels := by
      have hz : ∀ j, raw34756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34756step0 = (fun i j => raw34756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34756step0 raw34756; decide +kernel
      have hl : raw34756step0Labels = raw34756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34756 raw34756Labels permutation346 hz
    mixedMoment B raw34756step0 raw34756step0Labels = mixedMoment B raw34756step1 raw34756step1Labels := by
      have ha : raw34756step1 = (fun i j => raw34756step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34756step1 raw34756step0; decide +kernel
      have hl : raw34756step1Labels = raw34756step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34756step0 raw34756step0Labels permutation35 permutation4
    mixedMoment B raw34756step1 raw34756step1Labels = mixedMoment B raw34756step2 raw34756step2Labels := by
      have ha : raw34756step2 = -raw34756step1 := by apply Matrix.ext; change ∀ i j, raw34756step2 i j = -(raw34756step1 i j); unfold raw34756step2 raw34756step1; decide +kernel
      have hl : raw34756step2Labels = raw34756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3115 node3115Labels := by rfl

def raw34757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw34757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw34757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw34757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw34757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34757 raw34757Labels = mixedMoment B node2831 node2831Labels := by
  calc
    mixedMoment B raw34757 raw34757Labels = mixedMoment B raw34757step0 raw34757step0Labels := by
      have hz : ∀ j, raw34757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34757step0 = (fun i j => raw34757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34757step0 raw34757; decide +kernel
      have hl : raw34757step0Labels = raw34757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34757 raw34757Labels permutation346 hz
    mixedMoment B raw34757step0 raw34757step0Labels = mixedMoment B raw34757step1 raw34757step1Labels := by
      have ha : raw34757step1 = (fun i j => raw34757step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34757step1 raw34757step0; decide +kernel
      have hl : raw34757step1Labels = raw34757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34757step0 raw34757step0Labels permutation126 permutation2
    mixedMoment B raw34757step1 raw34757step1Labels = mixedMoment B raw34757step2 raw34757step2Labels := by
      have ha : raw34757step2 = -raw34757step1 := by apply Matrix.ext; change ∀ i j, raw34757step2 i j = -(raw34757step1 i j); unfold raw34757step2 raw34757step1; decide +kernel
      have hl : raw34757step2Labels = raw34757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2831 node2831Labels := by rfl

def raw34758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw34758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw34758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw34758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw34758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34758 raw34758Labels = mixedMoment B node2831 node2831Labels := by
  calc
    mixedMoment B raw34758 raw34758Labels = mixedMoment B raw34758step0 raw34758step0Labels := by
      have hz : ∀ j, raw34758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34758step0 = (fun i j => raw34758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34758step0 raw34758; decide +kernel
      have hl : raw34758step0Labels = raw34758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34758 raw34758Labels permutation346 hz
    mixedMoment B raw34758step0 raw34758step0Labels = mixedMoment B raw34758step1 raw34758step1Labels := by
      have ha : raw34758step1 = (fun i j => raw34758step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34758step1 raw34758step0; decide +kernel
      have hl : raw34758step1Labels = raw34758step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34758step0 raw34758step0Labels permutation150 permutation2
    mixedMoment B raw34758step1 raw34758step1Labels = mixedMoment B raw34758step2 raw34758step2Labels := by
      have ha : raw34758step2 = -raw34758step1 := by apply Matrix.ext; change ∀ i j, raw34758step2 i j = -(raw34758step1 i j); unfold raw34758step2 raw34758step1; decide +kernel
      have hl : raw34758step2Labels = raw34758step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2831 node2831Labels := by rfl

def raw34759 : Matrix (Fin 6) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]
def raw34759Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34759step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![1, -1], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1]]
def raw34759step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34759step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw34759step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34759 raw34759Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw34759 raw34759Labels = mixedMoment B raw34759step0 raw34759step0Labels := by
      have hz : ∀ j, raw34759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34759step0 = (fun i j => raw34759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34759step0 raw34759; decide +kernel
      have hl : raw34759step0Labels = raw34759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34759 raw34759Labels permutation346 hz
    mixedMoment B raw34759step0 raw34759step0Labels = mixedMoment B raw34759step1 raw34759step1Labels := by
      have ha : raw34759step1 = (fun i j => raw34759step0 (permutation62 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34759step1 raw34759step0; decide +kernel
      have hl : raw34759step1Labels = raw34759step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34759step0 raw34759step0Labels permutation62 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw34760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 2, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34760 raw34760Labels = mixedMoment B node2819 node2819Labels := by
  calc
    mixedMoment B raw34760 raw34760Labels = mixedMoment B raw34760step0 raw34760step0Labels := by
      have hz : ∀ j, raw34760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34760step0 = (fun i j => raw34760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34760step0 raw34760; decide +kernel
      have hl : raw34760step0Labels = raw34760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34760 raw34760Labels permutation346 hz
    mixedMoment B raw34760step0 raw34760step0Labels = mixedMoment B raw34760step1 raw34760step1Labels := by
      have ha : raw34760step1 = (fun i j => raw34760step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34760step1 raw34760step0; decide +kernel
      have hl : raw34760step1Labels = raw34760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34760step0 raw34760step0Labels permutation56 permutation2
    _ = mixedMoment B node2819 node2819Labels := by rfl

def raw34761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34761 raw34761Labels = mixedMoment B node3673 node3673Labels := by
  calc
    _ = mixedMoment B node3673 node3673Labels := by rfl

def raw34762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34762 raw34762Labels = mixedMoment B node3699 node3699Labels := by
  calc
    mixedMoment B raw34762 raw34762Labels = mixedMoment B raw34762step0 raw34762step0Labels := by
      have hz : ∀ j, raw34762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34762step0 = (fun i j => raw34762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34762step0 raw34762; decide +kernel
      have hl : raw34762step0Labels = raw34762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34762 raw34762Labels permutation346 hz
    _ = mixedMoment B node3699 node3699Labels := by rfl

def raw34763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34763 raw34763Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw34763 raw34763Labels = mixedMoment B raw34763step0 raw34763step0Labels := by
      have hz : ∀ j, raw34763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34763step0 = (fun i j => raw34763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34763step0 raw34763; decide +kernel
      have hl : raw34763step0Labels = raw34763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34763 raw34763Labels permutation346 hz
    mixedMoment B raw34763step0 raw34763step0Labels = mixedMoment B raw34763step1 raw34763step1Labels := by
      have ha : raw34763step1 = (fun i j => raw34763step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34763step1 raw34763step0; decide +kernel
      have hl : raw34763step1Labels = raw34763step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34763step0 raw34763step0Labels permutation34 permutation2
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw34764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34764 raw34764Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw34764 raw34764Labels = mixedMoment B raw34764step0 raw34764step0Labels := by
      have hz : ∀ j, raw34764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34764step0 = (fun i j => raw34764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34764step0 raw34764; decide +kernel
      have hl : raw34764step0Labels = raw34764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34764 raw34764Labels permutation346 hz
    mixedMoment B raw34764step0 raw34764step0Labels = mixedMoment B raw34764step1 raw34764step1Labels := by
      have ha : raw34764step1 = (fun i j => raw34764step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34764step1 raw34764step0; decide +kernel
      have hl : raw34764step1Labels = raw34764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34764step0 raw34764step0Labels permutation36 permutation2
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw34765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34765 raw34765Labels = mixedMoment B node2801 node2801Labels := by
  calc
    mixedMoment B raw34765 raw34765Labels = mixedMoment B raw34765step0 raw34765step0Labels := by
      have ha : raw34765step0 = (fun i j => raw34765 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34765step0 raw34765; decide +kernel
      have hl : raw34765step0Labels = raw34765Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34765 raw34765Labels permutation271 permutation2
    _ = mixedMoment B node2801 node2801Labels := by rfl

def raw34766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34766 raw34766Labels = mixedMoment B node3685 node3685Labels := by
  calc
    _ = mixedMoment B node3685 node3685Labels := by rfl

def raw34767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34767 raw34767Labels = mixedMoment B node3676 node3676Labels := by
  calc
    mixedMoment B raw34767 raw34767Labels = mixedMoment B raw34767step0 raw34767step0Labels := by
      have ha : raw34767step0 = (fun i j => raw34767 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34767step0 raw34767; decide +kernel
      have hl : raw34767step0Labels = raw34767Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34767 raw34767Labels permutation158 permutation2
    _ = mixedMoment B node3676 node3676Labels := by rfl

def raw34768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34768 raw34768Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw34768 raw34768Labels = mixedMoment B raw34768step0 raw34768step0Labels := by
      have ha : raw34768step0 = (fun i j => raw34768 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34768step0 raw34768; decide +kernel
      have hl : raw34768step0Labels = raw34768Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34768 raw34768Labels permutation160 permutation2
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw34769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34769 raw34769Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw34769 raw34769Labels = mixedMoment B raw34769step0 raw34769step0Labels := by
      have ha : raw34769step0 = (fun i j => raw34769 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34769step0 raw34769; decide +kernel
      have hl : raw34769step0Labels = raw34769Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34769 raw34769Labels permutation159 permutation2
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw34770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34770 raw34770Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw34770 raw34770Labels = mixedMoment B raw34770step0 raw34770step0Labels := by
      have ha : raw34770step0 = (fun i j => raw34770 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34770step0 raw34770; decide +kernel
      have hl : raw34770step0Labels = raw34770Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34770 raw34770Labels permutation687 permutation2
    mixedMoment B raw34770step0 raw34770step0Labels = mixedMoment B raw34770step1 raw34770step1Labels := by
      have ha : raw34770step1 = -raw34770step0 := by apply Matrix.ext; change ∀ i j, raw34770step1 i j = -(raw34770step0 i j); unfold raw34770step1 raw34770step0; decide +kernel
      have hl : raw34770step1Labels = raw34770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3722 node3722Labels := by rfl

def raw34771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34771 raw34771Labels = mixedMoment B node3715 node3715Labels := by
  calc
    _ = mixedMoment B node3715 node3715Labels := by rfl

def raw34772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34772 raw34772Labels = mixedMoment B node3708 node3708Labels := by
  calc
    _ = mixedMoment B node3708 node3708Labels := by rfl

def raw34773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw34773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34773 raw34773Labels = mixedMoment B node3134 node3134Labels := by
  calc
    mixedMoment B raw34773 raw34773Labels = mixedMoment B raw34773step0 raw34773step0Labels := by
      have ha : raw34773step0 = (fun i j => raw34773 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34773step0 raw34773; decide +kernel
      have hl : raw34773step0Labels = raw34773Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34773 raw34773Labels permutation589 permutation2
    mixedMoment B raw34773step0 raw34773step0Labels = mixedMoment B raw34773step1 raw34773step1Labels := by
      have ha : raw34773step1 = -raw34773step0 := by apply Matrix.ext; change ∀ i j, raw34773step1 i j = -(raw34773step0 i j); unfold raw34773step1 raw34773step0; decide +kernel
      have hl : raw34773step1Labels = raw34773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3134 node3134Labels := by rfl

def raw34774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34774 raw34774Labels = mixedMoment B node2350 node2350Labels := by
  calc
    mixedMoment B raw34774 raw34774Labels = mixedMoment B raw34774step0 raw34774step0Labels := by
      have ha : raw34774step0 = (fun i j => raw34774 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34774step0 raw34774; decide +kernel
      have hl : raw34774step0Labels = raw34774Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34774 raw34774Labels permutation688 permutation2
    mixedMoment B raw34774step0 raw34774step0Labels = mixedMoment B raw34774step1 raw34774step1Labels := by
      have ha : raw34774step1 = -raw34774step0 := by apply Matrix.ext; change ∀ i j, raw34774step1 i j = -(raw34774step0 i j); unfold raw34774step1 raw34774step0; decide +kernel
      have hl : raw34774step1Labels = raw34774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2350 node2350Labels := by rfl

def raw34775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34775 raw34775Labels = mixedMoment B node3922 node3922Labels := by
  calc
    mixedMoment B raw34775 raw34775Labels = mixedMoment B raw34775step0 raw34775step0Labels := by
      have ha : raw34775step0 = (fun i j => raw34775 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34775step0 raw34775; decide +kernel
      have hl : raw34775step0Labels = raw34775Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34775 raw34775Labels permutation588 permutation2
    mixedMoment B raw34775step0 raw34775step0Labels = mixedMoment B raw34775step1 raw34775step1Labels := by
      have ha : raw34775step1 = -raw34775step0 := by apply Matrix.ext; change ∀ i j, raw34775step1 i j = -(raw34775step0 i j); unfold raw34775step1 raw34775step0; decide +kernel
      have hl : raw34775step1Labels = raw34775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3922 node3922Labels := by rfl

def raw34776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34776 raw34776Labels = mixedMoment B node3716 node3716Labels := by
  calc
    _ = mixedMoment B node3716 node3716Labels := by rfl

def raw34777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34777 raw34777Labels = mixedMoment B node3709 node3709Labels := by
  calc
    _ = mixedMoment B node3709 node3709Labels := by rfl

def raw34778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw34778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34778 raw34778Labels = mixedMoment B node2824 node2824Labels := by
  calc
    mixedMoment B raw34778 raw34778Labels = mixedMoment B raw34778step0 raw34778step0Labels := by
      have ha : raw34778step0 = (fun i j => raw34778 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34778step0 raw34778; decide +kernel
      have hl : raw34778step0Labels = raw34778Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34778 raw34778Labels permutation589 permutation2
    mixedMoment B raw34778step0 raw34778step0Labels = mixedMoment B raw34778step1 raw34778step1Labels := by
      have ha : raw34778step1 = -raw34778step0 := by apply Matrix.ext; change ∀ i j, raw34778step1 i j = -(raw34778step0 i j); unfold raw34778step1 raw34778step0; decide +kernel
      have hl : raw34778step1Labels = raw34778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2824 node2824Labels := by rfl

def raw34779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34779 raw34779Labels = mixedMoment B node2824 node2824Labels := by
  calc
    mixedMoment B raw34779 raw34779Labels = mixedMoment B raw34779step0 raw34779step0Labels := by
      have ha : raw34779step0 = (fun i j => raw34779 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34779step0 raw34779; decide +kernel
      have hl : raw34779step0Labels = raw34779Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34779 raw34779Labels permutation688 permutation2
    mixedMoment B raw34779step0 raw34779step0Labels = mixedMoment B raw34779step1 raw34779step1Labels := by
      have ha : raw34779step1 = -raw34779step0 := by apply Matrix.ext; change ∀ i j, raw34779step1 i j = -(raw34779step0 i j); unfold raw34779step1 raw34779step0; decide +kernel
      have hl : raw34779step1Labels = raw34779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2824 node2824Labels := by rfl

def raw34780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34780 raw34780Labels = mixedMoment B node3135 node3135Labels := by
  calc
    mixedMoment B raw34780 raw34780Labels = mixedMoment B raw34780step0 raw34780step0Labels := by
      have ha : raw34780step0 = (fun i j => raw34780 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34780step0 raw34780; decide +kernel
      have hl : raw34780step0Labels = raw34780Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34780 raw34780Labels permutation265 permutation2
    _ = mixedMoment B node3135 node3135Labels := by rfl

def raw34781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34781 raw34781Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw34781 raw34781Labels = mixedMoment B raw34781step0 raw34781step0Labels := by
      have ha : raw34781step0 = (fun i j => raw34781 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34781step0 raw34781; decide +kernel
      have hl : raw34781step0Labels = raw34781Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34781 raw34781Labels permutation153 permutation2
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw34782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34782step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34782step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34782step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34782step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34782 raw34782Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw34782 raw34782Labels = mixedMoment B raw34782step0 raw34782step0Labels := by
      have hz : ∀ j, raw34782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34782step0 = (fun i j => raw34782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34782step0 raw34782; decide +kernel
      have hl : raw34782step0Labels = raw34782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34782 raw34782Labels permutation434 hz
    mixedMoment B raw34782step0 raw34782step0Labels = mixedMoment B raw34782step1 raw34782step1Labels := by
      have hz : ∀ j, raw34782step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34782step1 = (fun i j => raw34782step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34782step1 raw34782step0; decide +kernel
      have hl : raw34782step1Labels = raw34782step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34782step0 raw34782step0Labels permutation80 hz
    mixedMoment B raw34782step1 raw34782step1Labels = mixedMoment B raw34782step2 raw34782step2Labels := by
      have ha : raw34782step2 = (fun i j => raw34782step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34782step2 raw34782step1; decide +kernel
      have hl : raw34782step2Labels = raw34782step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34782step1 raw34782step1Labels permutation15 permutation3
    mixedMoment B raw34782step2 raw34782step2Labels = mixedMoment B raw34782step3 raw34782step3Labels := by
      have ha : raw34782step3 = raw34782step2 := by apply Matrix.ext; unfold raw34782step3 raw34782step2; decide +kernel
      have hl : raw34782step2Labels = labelEmbedding6 ∘ raw34782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34782step2 raw34782step2Labels raw34782step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw34783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34783step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34783step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34783step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34783 raw34783Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw34783 raw34783Labels = mixedMoment B raw34783step0 raw34783step0Labels := by
      have hz : ∀ j, raw34783 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34783step0 = (fun i j => raw34783 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34783step0 raw34783; decide +kernel
      have hl : raw34783step0Labels = raw34783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34783 raw34783Labels permutation434 hz
    mixedMoment B raw34783step0 raw34783step0Labels = mixedMoment B raw34783step1 raw34783step1Labels := by
      have ha : raw34783step1 = (fun i j => raw34783step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34783step1 raw34783step0; decide +kernel
      have hl : raw34783step1Labels = raw34783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34783step0 raw34783step0Labels permutation123 permutation3
    mixedMoment B raw34783step1 raw34783step1Labels = mixedMoment B raw34783step2 raw34783step2Labels := by
      have ha : raw34783step2 = -raw34783step1 := by apply Matrix.ext; change ∀ i j, raw34783step2 i j = -(raw34783step1 i j); unfold raw34783step2 raw34783step1; decide +kernel
      have hl : raw34783step2Labels = raw34783step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34783step2 raw34783step2Labels = mixedMoment B raw34783step3 raw34783step3Labels := by
      have ha : raw34783step3 = raw34783step2 := by apply Matrix.ext; unfold raw34783step3 raw34783step2; decide +kernel
      have hl : raw34783step2Labels = labelEmbedding6 ∘ raw34783step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34783step2 raw34783step2Labels raw34783step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw34784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34784step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34784step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34784step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34784 raw34784Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw34784 raw34784Labels = mixedMoment B raw34784step0 raw34784step0Labels := by
      have hz : ∀ j, raw34784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34784step0 = (fun i j => raw34784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34784step0 raw34784; decide +kernel
      have hl : raw34784step0Labels = raw34784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34784 raw34784Labels permutation346 hz
    mixedMoment B raw34784step0 raw34784step0Labels = mixedMoment B raw34784step1 raw34784step1Labels := by
      have ha : raw34784step1 = (fun i j => raw34784step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34784step1 raw34784step0; decide +kernel
      have hl : raw34784step1Labels = raw34784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34784step0 raw34784step0Labels permutation123 permutation3
    mixedMoment B raw34784step1 raw34784step1Labels = mixedMoment B raw34784step2 raw34784step2Labels := by
      have ha : raw34784step2 = -raw34784step1 := by apply Matrix.ext; change ∀ i j, raw34784step2 i j = -(raw34784step1 i j); unfold raw34784step2 raw34784step1; decide +kernel
      have hl : raw34784step2Labels = raw34784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34784step2 raw34784step2Labels = mixedMoment B raw34784step3 raw34784step3Labels := by
      have ha : raw34784step3 = raw34784step2 := by apply Matrix.ext; unfold raw34784step3 raw34784step2; decide +kernel
      have hl : raw34784step2Labels = labelEmbedding6 ∘ raw34784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34784step2 raw34784step2Labels raw34784step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw34785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34785step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34785step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34785step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34785 raw34785Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw34785 raw34785Labels = mixedMoment B raw34785step0 raw34785step0Labels := by
      have hz : ∀ j, raw34785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34785step0 = (fun i j => raw34785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34785step0 raw34785; decide +kernel
      have hl : raw34785step0Labels = raw34785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34785 raw34785Labels permutation434 hz
    mixedMoment B raw34785step0 raw34785step0Labels = mixedMoment B raw34785step1 raw34785step1Labels := by
      have hz : ∀ j, raw34785step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34785step1 = (fun i j => raw34785step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34785step1 raw34785step0; decide +kernel
      have hl : raw34785step1Labels = raw34785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34785step0 raw34785step0Labels permutation80 hz
    mixedMoment B raw34785step1 raw34785step1Labels = mixedMoment B raw34785step2 raw34785step2Labels := by
      have ha : raw34785step2 = (fun i j => raw34785step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34785step2 raw34785step1; decide +kernel
      have hl : raw34785step2Labels = raw34785step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34785step1 raw34785step1Labels permutation15 permutation3
    mixedMoment B raw34785step2 raw34785step2Labels = mixedMoment B raw34785step3 raw34785step3Labels := by
      have ha : raw34785step3 = raw34785step2 := by apply Matrix.ext; unfold raw34785step3 raw34785step2; decide +kernel
      have hl : raw34785step2Labels = labelEmbedding6 ∘ raw34785step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34785step2 raw34785step2Labels raw34785step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw34786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34786step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34786step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34786 raw34786Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw34786 raw34786Labels = mixedMoment B raw34786step0 raw34786step0Labels := by
      have hz : ∀ j, raw34786 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34786step0 = (fun i j => raw34786 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34786step0 raw34786; decide +kernel
      have hl : raw34786step0Labels = raw34786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34786 raw34786Labels permutation434 hz
    mixedMoment B raw34786step0 raw34786step0Labels = mixedMoment B raw34786step1 raw34786step1Labels := by
      have ha : raw34786step1 = (fun i j => raw34786step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34786step1 raw34786step0; decide +kernel
      have hl : raw34786step1Labels = raw34786step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34786step0 raw34786step0Labels permutation57 permutation3
    mixedMoment B raw34786step1 raw34786step1Labels = mixedMoment B raw34786step2 raw34786step2Labels := by
      have ha : raw34786step2 = raw34786step1 := by apply Matrix.ext; unfold raw34786step2 raw34786step1; decide +kernel
      have hl : raw34786step1Labels = labelEmbedding6 ∘ raw34786step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34786step1 raw34786step1Labels raw34786step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw34787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34787step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34787 raw34787Labels = mixedMoment B node5372 node5372Labels := by
  calc
    mixedMoment B raw34787 raw34787Labels = mixedMoment B raw34787step0 raw34787step0Labels := by
      have ha : raw34787step0 = (fun i j => raw34787 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34787step0 raw34787; decide +kernel
      have hl : raw34787step0Labels = raw34787Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34787 raw34787Labels permutation272 permutation3
    mixedMoment B raw34787step0 raw34787step0Labels = mixedMoment B raw34787step1 raw34787step1Labels := by
      have ha : raw34787step1 = raw34787step0 := by apply Matrix.ext; unfold raw34787step1 raw34787step0; decide +kernel
      have hl : raw34787step0Labels = labelEmbedding6 ∘ raw34787step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34787step0 raw34787step0Labels raw34787step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5372 node5372Labels := by rfl

def raw34788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34788step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34788 raw34788Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw34788 raw34788Labels = mixedMoment B raw34788step0 raw34788step0Labels := by
      have hz : ∀ j, raw34788 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34788step0 = (fun i j => raw34788 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34788step0 raw34788; decide +kernel
      have hl : raw34788step0Labels = raw34788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34788 raw34788Labels permutation434 hz
    mixedMoment B raw34788step0 raw34788step0Labels = mixedMoment B raw34788step1 raw34788step1Labels := by
      have ha : raw34788step1 = (fun i j => raw34788step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34788step1 raw34788step0; decide +kernel
      have hl : raw34788step1Labels = raw34788step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34788step0 raw34788step0Labels permutation60 permutation3
    mixedMoment B raw34788step1 raw34788step1Labels = mixedMoment B raw34788step2 raw34788step2Labels := by
      have ha : raw34788step2 = raw34788step1 := by apply Matrix.ext; unfold raw34788step2 raw34788step1; decide +kernel
      have hl : raw34788step1Labels = labelEmbedding6 ∘ raw34788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34788step1 raw34788step1Labels raw34788step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw34789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34789step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34789 raw34789Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw34789 raw34789Labels = mixedMoment B raw34789step0 raw34789step0Labels := by
      have hz : ∀ j, raw34789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34789step0 = (fun i j => raw34789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34789step0 raw34789; decide +kernel
      have hl : raw34789step0Labels = raw34789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34789 raw34789Labels permutation346 hz
    mixedMoment B raw34789step0 raw34789step0Labels = mixedMoment B raw34789step1 raw34789step1Labels := by
      have ha : raw34789step1 = (fun i j => raw34789step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34789step1 raw34789step0; decide +kernel
      have hl : raw34789step1Labels = raw34789step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34789step0 raw34789step0Labels permutation57 permutation3
    mixedMoment B raw34789step1 raw34789step1Labels = mixedMoment B raw34789step2 raw34789step2Labels := by
      have ha : raw34789step2 = raw34789step1 := by apply Matrix.ext; unfold raw34789step2 raw34789step1; decide +kernel
      have hl : raw34789step1Labels = labelEmbedding6 ∘ raw34789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34789step1 raw34789step1Labels raw34789step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw34790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34790step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34790 raw34790Labels = mixedMoment B node5372 node5372Labels := by
  calc
    mixedMoment B raw34790 raw34790Labels = mixedMoment B raw34790step0 raw34790step0Labels := by
      have ha : raw34790step0 = (fun i j => raw34790 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34790step0 raw34790; decide +kernel
      have hl : raw34790step0Labels = raw34790Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34790 raw34790Labels permutation266 permutation3
    mixedMoment B raw34790step0 raw34790step0Labels = mixedMoment B raw34790step1 raw34790step1Labels := by
      have ha : raw34790step1 = raw34790step0 := by apply Matrix.ext; unfold raw34790step1 raw34790step0; decide +kernel
      have hl : raw34790step0Labels = labelEmbedding6 ∘ raw34790step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34790step0 raw34790step0Labels raw34790step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5372 node5372Labels := by rfl

def raw34791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw34791step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw34791step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34791 raw34791Labels = mixedMoment B node4691 node4691Labels := by
  calc
    mixedMoment B raw34791 raw34791Labels = mixedMoment B raw34791step0 raw34791step0Labels := by
      have hz : ∀ j, raw34791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34791step0 = (fun i j => raw34791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34791step0 raw34791; decide +kernel
      have hl : raw34791step0Labels = raw34791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34791 raw34791Labels permutation434 hz
    mixedMoment B raw34791step0 raw34791step0Labels = mixedMoment B raw34791step1 raw34791step1Labels := by
      have hz : ∀ j, raw34791step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34791step1 = (fun i j => raw34791step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34791step1 raw34791step0; decide +kernel
      have hl : raw34791step1Labels = raw34791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34791step0 raw34791step0Labels permutation80 hz
    mixedMoment B raw34791step1 raw34791step1Labels = mixedMoment B raw34791step2 raw34791step2Labels := by
      have ha : raw34791step2 = (fun i j => raw34791step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34791step2 raw34791step1; decide +kernel
      have hl : raw34791step2Labels = raw34791step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34791step1 raw34791step1Labels permutation15 permutation3
    mixedMoment B raw34791step2 raw34791step2Labels = mixedMoment B raw34791step3 raw34791step3Labels := by
      have ha : raw34791step3 = raw34791step2 := by apply Matrix.ext; unfold raw34791step3 raw34791step2; decide +kernel
      have hl : raw34791step2Labels = labelEmbedding6 ∘ raw34791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34791step2 raw34791step2Labels raw34791step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4691 node4691Labels := by rfl

def raw34792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34792step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34792step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34792 raw34792Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw34792 raw34792Labels = mixedMoment B raw34792step0 raw34792step0Labels := by
      have hz : ∀ j, raw34792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34792step0 = (fun i j => raw34792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34792step0 raw34792; decide +kernel
      have hl : raw34792step0Labels = raw34792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34792 raw34792Labels permutation434 hz
    mixedMoment B raw34792step0 raw34792step0Labels = mixedMoment B raw34792step1 raw34792step1Labels := by
      have ha : raw34792step1 = (fun i j => raw34792step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34792step1 raw34792step0; decide +kernel
      have hl : raw34792step1Labels = raw34792step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34792step0 raw34792step0Labels permutation126 permutation3
    mixedMoment B raw34792step1 raw34792step1Labels = mixedMoment B raw34792step2 raw34792step2Labels := by
      have ha : raw34792step2 = -raw34792step1 := by apply Matrix.ext; change ∀ i j, raw34792step2 i j = -(raw34792step1 i j); unfold raw34792step2 raw34792step1; decide +kernel
      have hl : raw34792step2Labels = raw34792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34792step2 raw34792step2Labels = mixedMoment B raw34792step3 raw34792step3Labels := by
      have ha : raw34792step3 = raw34792step2 := by apply Matrix.ext; unfold raw34792step3 raw34792step2; decide +kernel
      have hl : raw34792step2Labels = labelEmbedding6 ∘ raw34792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34792step2 raw34792step2Labels raw34792step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw34793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34793step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34793step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34793step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34793 raw34793Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw34793 raw34793Labels = mixedMoment B raw34793step0 raw34793step0Labels := by
      have hz : ∀ j, raw34793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34793step0 = (fun i j => raw34793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34793step0 raw34793; decide +kernel
      have hl : raw34793step0Labels = raw34793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34793 raw34793Labels permutation346 hz
    mixedMoment B raw34793step0 raw34793step0Labels = mixedMoment B raw34793step1 raw34793step1Labels := by
      have ha : raw34793step1 = (fun i j => raw34793step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34793step1 raw34793step0; decide +kernel
      have hl : raw34793step1Labels = raw34793step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34793step0 raw34793step0Labels permutation126 permutation3
    mixedMoment B raw34793step1 raw34793step1Labels = mixedMoment B raw34793step2 raw34793step2Labels := by
      have ha : raw34793step2 = -raw34793step1 := by apply Matrix.ext; change ∀ i j, raw34793step2 i j = -(raw34793step1 i j); unfold raw34793step2 raw34793step1; decide +kernel
      have hl : raw34793step2Labels = raw34793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34793step2 raw34793step2Labels = mixedMoment B raw34793step3 raw34793step3Labels := by
      have ha : raw34793step3 = raw34793step2 := by apply Matrix.ext; unfold raw34793step3 raw34793step2; decide +kernel
      have hl : raw34793step2Labels = labelEmbedding6 ∘ raw34793step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34793step2 raw34793step2Labels raw34793step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw34794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34794step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34794step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34794step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34794step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34794step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34794 raw34794Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw34794 raw34794Labels = mixedMoment B raw34794step0 raw34794step0Labels := by
      have hz : ∀ j, raw34794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34794step0 = (fun i j => raw34794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34794step0 raw34794; decide +kernel
      have hl : raw34794step0Labels = raw34794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34794 raw34794Labels permutation434 hz
    mixedMoment B raw34794step0 raw34794step0Labels = mixedMoment B raw34794step1 raw34794step1Labels := by
      have hz : ∀ j, raw34794step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34794step1 = (fun i j => raw34794step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34794step1 raw34794step0; decide +kernel
      have hl : raw34794step1Labels = raw34794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34794step0 raw34794step0Labels permutation80 hz
    mixedMoment B raw34794step1 raw34794step1Labels = mixedMoment B raw34794step2 raw34794step2Labels := by
      have ha : raw34794step2 = (fun i j => raw34794step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34794step2 raw34794step1; decide +kernel
      have hl : raw34794step2Labels = raw34794step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34794step1 raw34794step1Labels permutation24 permutation3
    mixedMoment B raw34794step2 raw34794step2Labels = mixedMoment B raw34794step3 raw34794step3Labels := by
      have ha : raw34794step3 = -raw34794step2 := by apply Matrix.ext; change ∀ i j, raw34794step3 i j = -(raw34794step2 i j); unfold raw34794step3 raw34794step2; decide +kernel
      have hl : raw34794step3Labels = raw34794step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34794step3 raw34794step3Labels = mixedMoment B raw34794step4 raw34794step4Labels := by
      have ha : raw34794step4 = raw34794step3 := by apply Matrix.ext; unfold raw34794step4 raw34794step3; decide +kernel
      have hl : raw34794step3Labels = labelEmbedding6 ∘ raw34794step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34794step3 raw34794step3Labels raw34794step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw34795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw34795step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34795step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw34795step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34795 raw34795Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw34795 raw34795Labels = mixedMoment B raw34795step0 raw34795step0Labels := by
      have hz : ∀ j, raw34795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34795step0 = (fun i j => raw34795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34795step0 raw34795; decide +kernel
      have hl : raw34795step0Labels = raw34795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34795 raw34795Labels permutation434 hz
    mixedMoment B raw34795step0 raw34795step0Labels = mixedMoment B raw34795step1 raw34795step1Labels := by
      have hz : ∀ j, raw34795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34795step1 = (fun i j => raw34795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34795step1 raw34795step0; decide +kernel
      have hl : raw34795step1Labels = raw34795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34795step0 raw34795step0Labels permutation80 hz
    mixedMoment B raw34795step1 raw34795step1Labels = mixedMoment B raw34795step2 raw34795step2Labels := by
      have ha : raw34795step2 = (fun i j => raw34795step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34795step2 raw34795step1; decide +kernel
      have hl : raw34795step2Labels = raw34795step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34795step1 raw34795step1Labels permutation14 permutation3
    mixedMoment B raw34795step2 raw34795step2Labels = mixedMoment B raw34795step3 raw34795step3Labels := by
      have ha : raw34795step3 = raw34795step2 := by apply Matrix.ext; unfold raw34795step3 raw34795step2; decide +kernel
      have hl : raw34795step2Labels = labelEmbedding6 ∘ raw34795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34795step2 raw34795step2Labels raw34795step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4693 node4693Labels := by rfl

def raw34796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34796 raw34796Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw34796 raw34796Labels = mixedMoment B raw34796step0 raw34796step0Labels := by
      have hz : ∀ j, raw34796 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34796step0 = (fun i j => raw34796 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34796step0 raw34796; decide +kernel
      have hl : raw34796step0Labels = raw34796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34796 raw34796Labels permutation434 hz
    mixedMoment B raw34796step0 raw34796step0Labels = mixedMoment B raw34796step1 raw34796step1Labels := by
      have ha : raw34796step1 = (fun i j => raw34796step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34796step1 raw34796step0; decide +kernel
      have hl : raw34796step1Labels = raw34796step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34796step0 raw34796step0Labels permutation151 permutation2
    mixedMoment B raw34796step1 raw34796step1Labels = mixedMoment B raw34796step2 raw34796step2Labels := by
      have ha : raw34796step2 = -raw34796step1 := by apply Matrix.ext; change ∀ i j, raw34796step2 i j = -(raw34796step1 i j); unfold raw34796step2 raw34796step1; decide +kernel
      have hl : raw34796step2Labels = raw34796step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4973 node4973Labels := by rfl

def raw34797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34797 raw34797Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw34797 raw34797Labels = mixedMoment B raw34797step0 raw34797step0Labels := by
      have hz : ∀ j, raw34797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34797step0 = (fun i j => raw34797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34797step0 raw34797; decide +kernel
      have hl : raw34797step0Labels = raw34797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34797 raw34797Labels permutation346 hz
    mixedMoment B raw34797step0 raw34797step0Labels = mixedMoment B raw34797step1 raw34797step1Labels := by
      have ha : raw34797step1 = (fun i j => raw34797step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34797step1 raw34797step0; decide +kernel
      have hl : raw34797step1Labels = raw34797step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34797step0 raw34797step0Labels permutation151 permutation2
    mixedMoment B raw34797step1 raw34797step1Labels = mixedMoment B raw34797step2 raw34797step2Labels := by
      have ha : raw34797step2 = -raw34797step1 := by apply Matrix.ext; change ∀ i j, raw34797step2 i j = -(raw34797step1 i j); unfold raw34797step2 raw34797step1; decide +kernel
      have hl : raw34797step2Labels = raw34797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4973 node4973Labels := by rfl

def raw34798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34798step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34798step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34798 raw34798Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw34798 raw34798Labels = mixedMoment B raw34798step0 raw34798step0Labels := by
      have hz : ∀ j, raw34798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34798step0 = (fun i j => raw34798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34798step0 raw34798; decide +kernel
      have hl : raw34798step0Labels = raw34798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34798 raw34798Labels permutation434 hz
    mixedMoment B raw34798step0 raw34798step0Labels = mixedMoment B raw34798step1 raw34798step1Labels := by
      have hz : ∀ j, raw34798step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34798step1 = (fun i j => raw34798step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34798step1 raw34798step0; decide +kernel
      have hl : raw34798step1Labels = raw34798step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34798step0 raw34798step0Labels permutation80 hz
    mixedMoment B raw34798step1 raw34798step1Labels = mixedMoment B raw34798step2 raw34798step2Labels := by
      have ha : raw34798step2 = (fun i j => raw34798step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34798step2 raw34798step1; decide +kernel
      have hl : raw34798step2Labels = raw34798step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34798step1 raw34798step1Labels permutation15 permutation3
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw34799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34799 raw34799Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw34799 raw34799Labels = mixedMoment B raw34799step0 raw34799step0Labels := by
      have hz : ∀ j, raw34799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34799step0 = (fun i j => raw34799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34799step0 raw34799; decide +kernel
      have hl : raw34799step0Labels = raw34799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34799 raw34799Labels permutation434 hz
    mixedMoment B raw34799step0 raw34799step0Labels = mixedMoment B raw34799step1 raw34799step1Labels := by
      have ha : raw34799step1 = (fun i j => raw34799step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34799step1 raw34799step0; decide +kernel
      have hl : raw34799step1Labels = raw34799step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34799step0 raw34799step0Labels permutation123 permutation3
    mixedMoment B raw34799step1 raw34799step1Labels = mixedMoment B raw34799step2 raw34799step2Labels := by
      have ha : raw34799step2 = -raw34799step1 := by apply Matrix.ext; change ∀ i j, raw34799step2 i j = -(raw34799step1 i j); unfold raw34799step2 raw34799step1; decide +kernel
      have hl : raw34799step2Labels = raw34799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw34800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34800 raw34800Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw34800 raw34800Labels = mixedMoment B raw34800step0 raw34800step0Labels := by
      have hz : ∀ j, raw34800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34800step0 = (fun i j => raw34800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34800step0 raw34800; decide +kernel
      have hl : raw34800step0Labels = raw34800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34800 raw34800Labels permutation346 hz
    mixedMoment B raw34800step0 raw34800step0Labels = mixedMoment B raw34800step1 raw34800step1Labels := by
      have ha : raw34800step1 = (fun i j => raw34800step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34800step1 raw34800step0; decide +kernel
      have hl : raw34800step1Labels = raw34800step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34800step0 raw34800step0Labels permutation123 permutation3
    mixedMoment B raw34800step1 raw34800step1Labels = mixedMoment B raw34800step2 raw34800step2Labels := by
      have ha : raw34800step2 = -raw34800step1 := by apply Matrix.ext; change ∀ i j, raw34800step2 i j = -(raw34800step1 i j); unfold raw34800step2 raw34800step1; decide +kernel
      have hl : raw34800step2Labels = raw34800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw34801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34801step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34801 raw34801Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw34801 raw34801Labels = mixedMoment B raw34801step0 raw34801step0Labels := by
      have hz : ∀ j, raw34801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34801step0 = (fun i j => raw34801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34801step0 raw34801; decide +kernel
      have hl : raw34801step0Labels = raw34801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34801 raw34801Labels permutation434 hz
    mixedMoment B raw34801step0 raw34801step0Labels = mixedMoment B raw34801step1 raw34801step1Labels := by
      have hz : ∀ j, raw34801step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34801step1 = (fun i j => raw34801step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34801step1 raw34801step0; decide +kernel
      have hl : raw34801step1Labels = raw34801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34801step0 raw34801step0Labels permutation80 hz
    mixedMoment B raw34801step1 raw34801step1Labels = mixedMoment B raw34801step2 raw34801step2Labels := by
      have ha : raw34801step2 = (fun i j => raw34801step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34801step2 raw34801step1; decide +kernel
      have hl : raw34801step2Labels = raw34801step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34801step1 raw34801step1Labels permutation14 permutation3
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw34802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34802step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34802 raw34802Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw34802 raw34802Labels = mixedMoment B raw34802step0 raw34802step0Labels := by
      have hz : ∀ j, raw34802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34802step0 = (fun i j => raw34802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34802step0 raw34802; decide +kernel
      have hl : raw34802step0Labels = raw34802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34802 raw34802Labels permutation434 hz
    mixedMoment B raw34802step0 raw34802step0Labels = mixedMoment B raw34802step1 raw34802step1Labels := by
      have hz : ∀ j, raw34802step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34802step1 = (fun i j => raw34802step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34802step1 raw34802step0; decide +kernel
      have hl : raw34802step1Labels = raw34802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34802step0 raw34802step0Labels permutation80 hz
    mixedMoment B raw34802step1 raw34802step1Labels = mixedMoment B raw34802step2 raw34802step2Labels := by
      have ha : raw34802step2 = (fun i j => raw34802step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34802step2 raw34802step1; decide +kernel
      have hl : raw34802step2Labels = raw34802step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34802step1 raw34802step1Labels permutation15 permutation3
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw34803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34803step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34803 raw34803Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw34803 raw34803Labels = mixedMoment B raw34803step0 raw34803step0Labels := by
      have hz : ∀ j, raw34803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34803step0 = (fun i j => raw34803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34803step0 raw34803; decide +kernel
      have hl : raw34803step0Labels = raw34803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34803 raw34803Labels permutation434 hz
    mixedMoment B raw34803step0 raw34803step0Labels = mixedMoment B raw34803step1 raw34803step1Labels := by
      have ha : raw34803step1 = (fun i j => raw34803step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34803step1 raw34803step0; decide +kernel
      have hl : raw34803step1Labels = raw34803step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34803step0 raw34803step0Labels permutation57 permutation3
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw34804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34804 raw34804Labels = mixedMoment B node3708 node3708Labels := by
  calc
    mixedMoment B raw34804 raw34804Labels = mixedMoment B raw34804step0 raw34804step0Labels := by
      have ha : raw34804step0 = (fun i j => raw34804 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34804step0 raw34804; decide +kernel
      have hl : raw34804step0Labels = raw34804Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34804 raw34804Labels permutation272 permutation3
    _ = mixedMoment B node3708 node3708Labels := by rfl

def raw34805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34805 raw34805Labels = mixedMoment B node3739 node3739Labels := by
  calc
    mixedMoment B raw34805 raw34805Labels = mixedMoment B raw34805step0 raw34805step0Labels := by
      have hz : ∀ j, raw34805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34805step0 = (fun i j => raw34805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34805step0 raw34805; decide +kernel
      have hl : raw34805step0Labels = raw34805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34805 raw34805Labels permutation434 hz
    mixedMoment B raw34805step0 raw34805step0Labels = mixedMoment B raw34805step1 raw34805step1Labels := by
      have ha : raw34805step1 = (fun i j => raw34805step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34805step1 raw34805step0; decide +kernel
      have hl : raw34805step1Labels = raw34805step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34805step0 raw34805step0Labels permutation56 permutation3
    _ = mixedMoment B node3739 node3739Labels := by rfl

def raw34806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34806 raw34806Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw34806 raw34806Labels = mixedMoment B raw34806step0 raw34806step0Labels := by
      have hz : ∀ j, raw34806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34806step0 = (fun i j => raw34806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34806step0 raw34806; decide +kernel
      have hl : raw34806step0Labels = raw34806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34806 raw34806Labels permutation434 hz
    mixedMoment B raw34806step0 raw34806step0Labels = mixedMoment B raw34806step1 raw34806step1Labels := by
      have ha : raw34806step1 = (fun i j => raw34806step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34806step1 raw34806step0; decide +kernel
      have hl : raw34806step1Labels = raw34806step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34806step0 raw34806step0Labels permutation60 permutation3
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw34807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34807 raw34807Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw34807 raw34807Labels = mixedMoment B raw34807step0 raw34807step0Labels := by
      have hz : ∀ j, raw34807 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34807step0 = (fun i j => raw34807 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34807step0 raw34807; decide +kernel
      have hl : raw34807step0Labels = raw34807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34807 raw34807Labels permutation346 hz
    mixedMoment B raw34807step0 raw34807step0Labels = mixedMoment B raw34807step1 raw34807step1Labels := by
      have ha : raw34807step1 = (fun i j => raw34807step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34807step1 raw34807step0; decide +kernel
      have hl : raw34807step1Labels = raw34807step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34807step0 raw34807step0Labels permutation57 permutation3
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw34808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34808 raw34808Labels = mixedMoment B node3708 node3708Labels := by
  calc
    mixedMoment B raw34808 raw34808Labels = mixedMoment B raw34808step0 raw34808step0Labels := by
      have ha : raw34808step0 = (fun i j => raw34808 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34808step0 raw34808; decide +kernel
      have hl : raw34808step0Labels = raw34808Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34808 raw34808Labels permutation266 permutation3
    _ = mixedMoment B node3708 node3708Labels := by rfl

def raw34809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34809 raw34809Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw34809 raw34809Labels = mixedMoment B raw34809step0 raw34809step0Labels := by
      have hz : ∀ j, raw34809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34809step0 = (fun i j => raw34809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34809step0 raw34809; decide +kernel
      have hl : raw34809step0Labels = raw34809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34809 raw34809Labels permutation346 hz
    mixedMoment B raw34809step0 raw34809step0Labels = mixedMoment B raw34809step1 raw34809step1Labels := by
      have ha : raw34809step1 = (fun i j => raw34809step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34809step1 raw34809step0; decide +kernel
      have hl : raw34809step1Labels = raw34809step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34809step0 raw34809step0Labels permutation60 permutation3
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw34810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw34810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34810 raw34810Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw34810 raw34810Labels = mixedMoment B raw34810step0 raw34810step0Labels := by
      have hz : ∀ j, raw34810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34810step0 = (fun i j => raw34810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34810step0 raw34810; decide +kernel
      have hl : raw34810step0Labels = raw34810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34810 raw34810Labels permutation434 hz
    mixedMoment B raw34810step0 raw34810step0Labels = mixedMoment B raw34810step1 raw34810step1Labels := by
      have hz : ∀ j, raw34810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34810step1 = (fun i j => raw34810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34810step1 raw34810step0; decide +kernel
      have hl : raw34810step1Labels = raw34810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34810step0 raw34810step0Labels permutation80 hz
    mixedMoment B raw34810step1 raw34810step1Labels = mixedMoment B raw34810step2 raw34810step2Labels := by
      have ha : raw34810step2 = (fun i j => raw34810step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34810step2 raw34810step1; decide +kernel
      have hl : raw34810step2Labels = raw34810step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34810step1 raw34810step1Labels permutation15 permutation3
    _ = mixedMoment B node1817 node1817Labels := by rfl

def raw34811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34811step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34811 raw34811Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw34811 raw34811Labels = mixedMoment B raw34811step0 raw34811step0Labels := by
      have hz : ∀ j, raw34811 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34811step0 = (fun i j => raw34811 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34811step0 raw34811; decide +kernel
      have hl : raw34811step0Labels = raw34811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34811 raw34811Labels permutation434 hz
    mixedMoment B raw34811step0 raw34811step0Labels = mixedMoment B raw34811step1 raw34811step1Labels := by
      have ha : raw34811step1 = (fun i j => raw34811step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34811step1 raw34811step0; decide +kernel
      have hl : raw34811step1Labels = raw34811step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34811step0 raw34811step0Labels permutation126 permutation3
    mixedMoment B raw34811step1 raw34811step1Labels = mixedMoment B raw34811step2 raw34811step2Labels := by
      have ha : raw34811step2 = -raw34811step1 := by apply Matrix.ext; change ∀ i j, raw34811step2 i j = -(raw34811step1 i j); unfold raw34811step2 raw34811step1; decide +kernel
      have hl : raw34811step2Labels = raw34811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw34812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw34812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34812 raw34812Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw34812 raw34812Labels = mixedMoment B raw34812step0 raw34812step0Labels := by
      have hz : ∀ j, raw34812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34812step0 = (fun i j => raw34812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34812step0 raw34812; decide +kernel
      have hl : raw34812step0Labels = raw34812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34812 raw34812Labels permutation346 hz
    mixedMoment B raw34812step0 raw34812step0Labels = mixedMoment B raw34812step1 raw34812step1Labels := by
      have ha : raw34812step1 = (fun i j => raw34812step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34812step1 raw34812step0; decide +kernel
      have hl : raw34812step1Labels = raw34812step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34812step0 raw34812step0Labels permutation126 permutation3
    mixedMoment B raw34812step1 raw34812step1Labels = mixedMoment B raw34812step2 raw34812step2Labels := by
      have ha : raw34812step2 = -raw34812step1 := by apply Matrix.ext; change ∀ i j, raw34812step2 i j = -(raw34812step1 i j); unfold raw34812step2 raw34812step1; decide +kernel
      have hl : raw34812step2Labels = raw34812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw34813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -3, 0], ![1, 1, -2]]
def raw34813step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34813 raw34813Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw34813 raw34813Labels = mixedMoment B raw34813step0 raw34813step0Labels := by
      have hz : ∀ j, raw34813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34813step0 = (fun i j => raw34813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34813step0 raw34813; decide +kernel
      have hl : raw34813step0Labels = raw34813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34813 raw34813Labels permutation434 hz
    mixedMoment B raw34813step0 raw34813step0Labels = mixedMoment B raw34813step1 raw34813step1Labels := by
      have hz : ∀ j, raw34813step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34813step1 = (fun i j => raw34813step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34813step1 raw34813step0; decide +kernel
      have hl : raw34813step1Labels = raw34813step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34813step0 raw34813step0Labels permutation80 hz
    mixedMoment B raw34813step1 raw34813step1Labels = mixedMoment B raw34813step2 raw34813step2Labels := by
      have ha : raw34813step2 = (fun i j => raw34813step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34813step2 raw34813step1; decide +kernel
      have hl : raw34813step2Labels = raw34813step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34813step1 raw34813step1Labels permutation24 permutation3
    mixedMoment B raw34813step2 raw34813step2Labels = mixedMoment B raw34813step3 raw34813step3Labels := by
      have ha : raw34813step3 = -raw34813step2 := by apply Matrix.ext; change ∀ i j, raw34813step3 i j = -(raw34813step2 i j); unfold raw34813step3 raw34813step2; decide +kernel
      have hl : raw34813step3Labels = raw34813step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw34814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34814step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw34814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34814 raw34814Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw34814 raw34814Labels = mixedMoment B raw34814step0 raw34814step0Labels := by
      have hz : ∀ j, raw34814 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34814step0 = (fun i j => raw34814 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34814step0 raw34814; decide +kernel
      have hl : raw34814step0Labels = raw34814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34814 raw34814Labels permutation434 hz
    mixedMoment B raw34814step0 raw34814step0Labels = mixedMoment B raw34814step1 raw34814step1Labels := by
      have hz : ∀ j, raw34814step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34814step1 = (fun i j => raw34814step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34814step1 raw34814step0; decide +kernel
      have hl : raw34814step1Labels = raw34814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34814step0 raw34814step0Labels permutation80 hz
    mixedMoment B raw34814step1 raw34814step1Labels = mixedMoment B raw34814step2 raw34814step2Labels := by
      have ha : raw34814step2 = (fun i j => raw34814step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34814step2 raw34814step1; decide +kernel
      have hl : raw34814step2Labels = raw34814step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34814step1 raw34814step1Labels permutation14 permutation3
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw34815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34815 raw34815Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw34815 raw34815Labels = mixedMoment B raw34815step0 raw34815step0Labels := by
      have hz : ∀ j, raw34815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34815step0 = (fun i j => raw34815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34815step0 raw34815; decide +kernel
      have hl : raw34815step0Labels = raw34815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34815 raw34815Labels permutation434 hz
    mixedMoment B raw34815step0 raw34815step0Labels = mixedMoment B raw34815step1 raw34815step1Labels := by
      have ha : raw34815step1 = (fun i j => raw34815step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34815step1 raw34815step0; decide +kernel
      have hl : raw34815step1Labels = raw34815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34815step0 raw34815step0Labels permutation150 permutation3
    mixedMoment B raw34815step1 raw34815step1Labels = mixedMoment B raw34815step2 raw34815step2Labels := by
      have ha : raw34815step2 = -raw34815step1 := by apply Matrix.ext; change ∀ i j, raw34815step2 i j = -(raw34815step1 i j); unfold raw34815step2 raw34815step1; decide +kernel
      have hl : raw34815step2Labels = raw34815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2817 node2817Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
