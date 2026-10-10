import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5760 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5760 raw5760Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5760 raw5760Labels = mixedMoment B raw5760step0 raw5760step0Labels := by
      have hz : ∀ j, raw5760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5760step0 = (fun i j => raw5760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5760step0 raw5760; decide +kernel
      have hl : raw5760step0Labels = raw5760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5760 raw5760Labels permutation265 hz
    mixedMoment B raw5760step0 raw5760step0Labels = mixedMoment B raw5760step1 raw5760step1Labels := by
      have ha : raw5760step1 = (fun i j => raw5760step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5760step1 raw5760step0; decide +kernel
      have hl : raw5760step1Labels = raw5760step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5760step0 raw5760step0Labels permutation50 permutation4
    mixedMoment B raw5760step1 raw5760step1Labels = mixedMoment B raw5760step2 raw5760step2Labels := by
      have ha : raw5760step2 = -raw5760step1 := by apply Matrix.ext; change ∀ i j, raw5760step2 i j = -(raw5760step1 i j); unfold raw5760step2 raw5760step1; decide +kernel
      have hl : raw5760step2Labels = raw5760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw5761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5761 raw5761Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5761 raw5761Labels = mixedMoment B raw5761step0 raw5761step0Labels := by
      have hz : ∀ j, raw5761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5761step0 = (fun i j => raw5761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5761step0 raw5761; decide +kernel
      have hl : raw5761step0Labels = raw5761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5761 raw5761Labels permutation346 hz
    mixedMoment B raw5761step0 raw5761step0Labels = mixedMoment B raw5761step1 raw5761step1Labels := by
      have ha : raw5761step1 = (fun i j => raw5761step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5761step1 raw5761step0; decide +kernel
      have hl : raw5761step1Labels = raw5761step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5761step0 raw5761step0Labels permutation50 permutation4
    mixedMoment B raw5761step1 raw5761step1Labels = mixedMoment B raw5761step2 raw5761step2Labels := by
      have ha : raw5761step2 = -raw5761step1 := by apply Matrix.ext; change ∀ i j, raw5761step2 i j = -(raw5761step1 i j); unfold raw5761step2 raw5761step1; decide +kernel
      have hl : raw5761step2Labels = raw5761step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw5762 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5762 raw5762Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5762 raw5762Labels = mixedMoment B raw5762step0 raw5762step0Labels := by
      have hz : ∀ j, raw5762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5762step0 = (fun i j => raw5762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5762step0 raw5762; decide +kernel
      have hl : raw5762step0Labels = raw5762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5762 raw5762Labels permutation434 hz
    mixedMoment B raw5762step0 raw5762step0Labels = mixedMoment B raw5762step1 raw5762step1Labels := by
      have ha : raw5762step1 = (fun i j => raw5762step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5762step1 raw5762step0; decide +kernel
      have hl : raw5762step1Labels = raw5762step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5762step0 raw5762step0Labels permutation50 permutation4
    mixedMoment B raw5762step1 raw5762step1Labels = mixedMoment B raw5762step2 raw5762step2Labels := by
      have ha : raw5762step2 = -raw5762step1 := by apply Matrix.ext; change ∀ i j, raw5762step2 i j = -(raw5762step1 i j); unfold raw5762step2 raw5762step1; decide +kernel
      have hl : raw5762step2Labels = raw5762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw5763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw5763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5763 raw5763Labels = mixedMoment B node2131 node2131Labels := by
  calc
    mixedMoment B raw5763 raw5763Labels = mixedMoment B raw5763step0 raw5763step0Labels := by
      have ha : raw5763step0 = (fun i j => raw5763 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5763step0 raw5763; decide +kernel
      have hl : raw5763step0Labels = raw5763Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5763 raw5763Labels permutation246 permutation4
    mixedMoment B raw5763step0 raw5763step0Labels = mixedMoment B raw5763step1 raw5763step1Labels := by
      have ha : raw5763step1 = -raw5763step0 := by apply Matrix.ext; change ∀ i j, raw5763step1 i j = -(raw5763step0 i j); unfold raw5763step1 raw5763step0; decide +kernel
      have hl : raw5763step1Labels = raw5763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2131 node2131Labels := by rfl

def raw5764 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5764 raw5764Labels = mixedMoment B node2095 node2095Labels := by
  calc
    mixedMoment B raw5764 raw5764Labels = mixedMoment B raw5764step0 raw5764step0Labels := by
      have ha : raw5764step0 = (fun i j => raw5764 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5764step0 raw5764; decide +kernel
      have hl : raw5764step0Labels = raw5764Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5764 raw5764Labels permutation243 permutation4
    mixedMoment B raw5764step0 raw5764step0Labels = mixedMoment B raw5764step1 raw5764step1Labels := by
      have ha : raw5764step1 = -raw5764step0 := by apply Matrix.ext; change ∀ i j, raw5764step1 i j = -(raw5764step0 i j); unfold raw5764step1 raw5764step0; decide +kernel
      have hl : raw5764step1Labels = raw5764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2095 node2095Labels := by rfl

def raw5765 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5765 raw5765Labels = mixedMoment B node2095 node2095Labels := by
  calc
    mixedMoment B raw5765 raw5765Labels = mixedMoment B raw5765step0 raw5765step0Labels := by
      have ha : raw5765step0 = (fun i j => raw5765 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5765step0 raw5765; decide +kernel
      have hl : raw5765step0Labels = raw5765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5765 raw5765Labels permutation241 permutation4
    mixedMoment B raw5765step0 raw5765step0Labels = mixedMoment B raw5765step1 raw5765step1Labels := by
      have ha : raw5765step1 = -raw5765step0 := by apply Matrix.ext; change ∀ i j, raw5765step1 i j = -(raw5765step0 i j); unfold raw5765step1 raw5765step0; decide +kernel
      have hl : raw5765step1Labels = raw5765step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2095 node2095Labels := by rfl

def raw5766 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw5766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5766 raw5766Labels = mixedMoment B node2095 node2095Labels := by
  calc
    mixedMoment B raw5766 raw5766Labels = mixedMoment B raw5766step0 raw5766step0Labels := by
      have ha : raw5766step0 = (fun i j => raw5766 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5766step0 raw5766; decide +kernel
      have hl : raw5766step0Labels = raw5766Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5766 raw5766Labels permutation240 permutation4
    mixedMoment B raw5766step0 raw5766step0Labels = mixedMoment B raw5766step1 raw5766step1Labels := by
      have ha : raw5766step1 = -raw5766step0 := by apply Matrix.ext; change ∀ i j, raw5766step1 i j = -(raw5766step0 i j); unfold raw5766step1 raw5766step0; decide +kernel
      have hl : raw5766step1Labels = raw5766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2095 node2095Labels := by rfl

def raw5767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw5767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5767 raw5767Labels = mixedMoment B node2104 node2104Labels := by
  calc
    mixedMoment B raw5767 raw5767Labels = mixedMoment B raw5767step0 raw5767step0Labels := by
      have ha : raw5767step0 = (fun i j => raw5767 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5767step0 raw5767; decide +kernel
      have hl : raw5767step0Labels = raw5767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5767 raw5767Labels permutation224 permutation4
    mixedMoment B raw5767step0 raw5767step0Labels = mixedMoment B raw5767step1 raw5767step1Labels := by
      have ha : raw5767step1 = -raw5767step0 := by apply Matrix.ext; change ∀ i j, raw5767step1 i j = -(raw5767step0 i j); unfold raw5767step1 raw5767step0; decide +kernel
      have hl : raw5767step1Labels = raw5767step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2104 node2104Labels := by rfl

def raw5768 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5768 raw5768Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5768 raw5768Labels = mixedMoment B raw5768step0 raw5768step0Labels := by
      have hz : ∀ j, raw5768 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5768step0 = (fun i j => raw5768 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5768step0 raw5768; decide +kernel
      have hl : raw5768step0Labels = raw5768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5768 raw5768Labels permutation265 hz
    mixedMoment B raw5768step0 raw5768step0Labels = mixedMoment B raw5768step1 raw5768step1Labels := by
      have ha : raw5768step1 = (fun i j => raw5768step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5768step1 raw5768step0; decide +kernel
      have hl : raw5768step1Labels = raw5768step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5768step0 raw5768step0Labels permutation44 permutation4
    mixedMoment B raw5768step1 raw5768step1Labels = mixedMoment B raw5768step2 raw5768step2Labels := by
      have ha : raw5768step2 = -raw5768step1 := by apply Matrix.ext; change ∀ i j, raw5768step2 i j = -(raw5768step1 i j); unfold raw5768step2 raw5768step1; decide +kernel
      have hl : raw5768step2Labels = raw5768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw5769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5769 raw5769Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5769 raw5769Labels = mixedMoment B raw5769step0 raw5769step0Labels := by
      have hz : ∀ j, raw5769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5769step0 = (fun i j => raw5769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5769step0 raw5769; decide +kernel
      have hl : raw5769step0Labels = raw5769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5769 raw5769Labels permutation346 hz
    mixedMoment B raw5769step0 raw5769step0Labels = mixedMoment B raw5769step1 raw5769step1Labels := by
      have ha : raw5769step1 = (fun i j => raw5769step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5769step1 raw5769step0; decide +kernel
      have hl : raw5769step1Labels = raw5769step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5769step0 raw5769step0Labels permutation44 permutation4
    mixedMoment B raw5769step1 raw5769step1Labels = mixedMoment B raw5769step2 raw5769step2Labels := by
      have ha : raw5769step2 = -raw5769step1 := by apply Matrix.ext; change ∀ i j, raw5769step2 i j = -(raw5769step1 i j); unfold raw5769step2 raw5769step1; decide +kernel
      have hl : raw5769step2Labels = raw5769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw5770 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5770 raw5770Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5770 raw5770Labels = mixedMoment B raw5770step0 raw5770step0Labels := by
      have hz : ∀ j, raw5770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5770step0 = (fun i j => raw5770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5770step0 raw5770; decide +kernel
      have hl : raw5770step0Labels = raw5770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5770 raw5770Labels permutation434 hz
    mixedMoment B raw5770step0 raw5770step0Labels = mixedMoment B raw5770step1 raw5770step1Labels := by
      have ha : raw5770step1 = (fun i j => raw5770step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5770step1 raw5770step0; decide +kernel
      have hl : raw5770step1Labels = raw5770step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5770step0 raw5770step0Labels permutation44 permutation4
    mixedMoment B raw5770step1 raw5770step1Labels = mixedMoment B raw5770step2 raw5770step2Labels := by
      have ha : raw5770step2 = -raw5770step1 := by apply Matrix.ext; change ∀ i j, raw5770step2 i j = -(raw5770step1 i j); unfold raw5770step2 raw5770step1; decide +kernel
      have hl : raw5770step2Labels = raw5770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw5771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5771step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5771 raw5771Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw5771 raw5771Labels = mixedMoment B raw5771step0 raw5771step0Labels := by
      have hz : ∀ j, raw5771 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5771step0 = (fun i j => raw5771 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5771step0 raw5771; decide +kernel
      have hl : raw5771step0Labels = raw5771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5771 raw5771Labels permutation434 hz
    mixedMoment B raw5771step0 raw5771step0Labels = mixedMoment B raw5771step1 raw5771step1Labels := by
      have hz : ∀ j, raw5771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5771step1 = (fun i j => raw5771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5771step1 raw5771step0; decide +kernel
      have hl : raw5771step1Labels = raw5771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5771step0 raw5771step0Labels permutation80 hz
    mixedMoment B raw5771step1 raw5771step1Labels = mixedMoment B raw5771step2 raw5771step2Labels := by
      have ha : raw5771step2 = (fun i j => raw5771step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5771step2 raw5771step1; decide +kernel
      have hl : raw5771step2Labels = raw5771step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5771step1 raw5771step1Labels permutation25 permutation6
    mixedMoment B raw5771step2 raw5771step2Labels = mixedMoment B raw5771step3 raw5771step3Labels := by
      have ha : raw5771step3 = raw5771step2 := by apply Matrix.ext; unfold raw5771step3 raw5771step2; decide +kernel
      have hl : raw5771step2Labels = labelEmbedding9 ∘ raw5771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5771step2 raw5771step2Labels raw5771step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw5772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5772step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5772 raw5772Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw5772 raw5772Labels = mixedMoment B raw5772step0 raw5772step0Labels := by
      have hz : ∀ j, raw5772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5772step0 = (fun i j => raw5772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5772step0 raw5772; decide +kernel
      have hl : raw5772step0Labels = raw5772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5772 raw5772Labels permutation434 hz
    mixedMoment B raw5772step0 raw5772step0Labels = mixedMoment B raw5772step1 raw5772step1Labels := by
      have ha : raw5772step1 = (fun i j => raw5772step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5772step1 raw5772step0; decide +kernel
      have hl : raw5772step1Labels = raw5772step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5772step0 raw5772step0Labels permutation121 permutation6
    mixedMoment B raw5772step1 raw5772step1Labels = mixedMoment B raw5772step2 raw5772step2Labels := by
      have ha : raw5772step2 = raw5772step1 := by apply Matrix.ext; unfold raw5772step2 raw5772step1; decide +kernel
      have hl : raw5772step1Labels = labelEmbedding9 ∘ raw5772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5772step1 raw5772step1Labels raw5772step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw5773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5773step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5773 raw5773Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw5773 raw5773Labels = mixedMoment B raw5773step0 raw5773step0Labels := by
      have hz : ∀ j, raw5773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5773step0 = (fun i j => raw5773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5773step0 raw5773; decide +kernel
      have hl : raw5773step0Labels = raw5773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5773 raw5773Labels permutation346 hz
    mixedMoment B raw5773step0 raw5773step0Labels = mixedMoment B raw5773step1 raw5773step1Labels := by
      have ha : raw5773step1 = (fun i j => raw5773step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5773step1 raw5773step0; decide +kernel
      have hl : raw5773step1Labels = raw5773step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5773step0 raw5773step0Labels permutation121 permutation6
    mixedMoment B raw5773step1 raw5773step1Labels = mixedMoment B raw5773step2 raw5773step2Labels := by
      have ha : raw5773step2 = raw5773step1 := by apply Matrix.ext; unfold raw5773step2 raw5773step1; decide +kernel
      have hl : raw5773step1Labels = labelEmbedding9 ∘ raw5773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5773step1 raw5773step1Labels raw5773step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw5774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5774step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5774step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5774step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5774step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5774step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5774 raw5774Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw5774 raw5774Labels = mixedMoment B raw5774step0 raw5774step0Labels := by
      have hz : ∀ j, raw5774 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5774step0 = (fun i j => raw5774 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5774step0 raw5774; decide +kernel
      have hl : raw5774step0Labels = raw5774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5774 raw5774Labels permutation434 hz
    mixedMoment B raw5774step0 raw5774step0Labels = mixedMoment B raw5774step1 raw5774step1Labels := by
      have hz : ∀ j, raw5774step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5774step1 = (fun i j => raw5774step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5774step1 raw5774step0; decide +kernel
      have hl : raw5774step1Labels = raw5774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5774step0 raw5774step0Labels permutation80 hz
    mixedMoment B raw5774step1 raw5774step1Labels = mixedMoment B raw5774step2 raw5774step2Labels := by
      have ha : raw5774step2 = (fun i j => raw5774step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5774step2 raw5774step1; decide +kernel
      have hl : raw5774step2Labels = raw5774step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5774step1 raw5774step1Labels permutation20 permutation4
    mixedMoment B raw5774step2 raw5774step2Labels = mixedMoment B raw5774step3 raw5774step3Labels := by
      have ha : raw5774step3 = -raw5774step2 := by apply Matrix.ext; change ∀ i j, raw5774step3 i j = -(raw5774step2 i j); unfold raw5774step3 raw5774step2; decide +kernel
      have hl : raw5774step3Labels = raw5774step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5774step3 raw5774step3Labels = mixedMoment B raw5774step4 raw5774step4Labels := by
      have ha : raw5774step4 = raw5774step3 := by apply Matrix.ext; unfold raw5774step4 raw5774step3; decide +kernel
      have hl : raw5774step3Labels = labelEmbedding7 ∘ raw5774step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5774step3 raw5774step3Labels raw5774step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw5775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5775step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5775 raw5775Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw5775 raw5775Labels = mixedMoment B raw5775step0 raw5775step0Labels := by
      have hz : ∀ j, raw5775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5775step0 = (fun i j => raw5775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5775step0 raw5775; decide +kernel
      have hl : raw5775step0Labels = raw5775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5775 raw5775Labels permutation434 hz
    mixedMoment B raw5775step0 raw5775step0Labels = mixedMoment B raw5775step1 raw5775step1Labels := by
      have hz : ∀ j, raw5775step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5775step1 = (fun i j => raw5775step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5775step1 raw5775step0; decide +kernel
      have hl : raw5775step1Labels = raw5775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5775step0 raw5775step0Labels permutation80 hz
    mixedMoment B raw5775step1 raw5775step1Labels = mixedMoment B raw5775step2 raw5775step2Labels := by
      have ha : raw5775step2 = (fun i j => raw5775step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5775step2 raw5775step1; decide +kernel
      have hl : raw5775step2Labels = raw5775step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5775step1 raw5775step1Labels permutation25 permutation6
    mixedMoment B raw5775step2 raw5775step2Labels = mixedMoment B raw5775step3 raw5775step3Labels := by
      have ha : raw5775step3 = raw5775step2 := by apply Matrix.ext; unfold raw5775step3 raw5775step2; decide +kernel
      have hl : raw5775step2Labels = labelEmbedding9 ∘ raw5775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5775step2 raw5775step2Labels raw5775step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw5776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw5776step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw5776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5776 raw5776Labels = mixedMoment B node4615 node4615Labels := by
  calc
    mixedMoment B raw5776 raw5776Labels = mixedMoment B raw5776step0 raw5776step0Labels := by
      have hz : ∀ j, raw5776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5776step0 = (fun i j => raw5776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5776step0 raw5776; decide +kernel
      have hl : raw5776step0Labels = raw5776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5776 raw5776Labels permutation434 hz
    mixedMoment B raw5776step0 raw5776step0Labels = mixedMoment B raw5776step1 raw5776step1Labels := by
      have hz : ∀ j, raw5776step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5776step1 = (fun i j => raw5776step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5776step1 raw5776step0; decide +kernel
      have hl : raw5776step1Labels = raw5776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5776step0 raw5776step0Labels permutation80 hz
    mixedMoment B raw5776step1 raw5776step1Labels = mixedMoment B raw5776step2 raw5776step2Labels := by
      have ha : raw5776step2 = (fun i j => raw5776step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5776step2 raw5776step1; decide +kernel
      have hl : raw5776step2Labels = raw5776step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5776step1 raw5776step1Labels permutation10 permutation3
    mixedMoment B raw5776step2 raw5776step2Labels = mixedMoment B raw5776step3 raw5776step3Labels := by
      have ha : raw5776step3 = raw5776step2 := by apply Matrix.ext; unfold raw5776step3 raw5776step2; decide +kernel
      have hl : raw5776step2Labels = labelEmbedding6 ∘ raw5776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5776step2 raw5776step2Labels raw5776step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4615 node4615Labels := by rfl

def raw5777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5777 raw5777Labels = mixedMoment B node5165 node5165Labels := by
  calc
    mixedMoment B raw5777 raw5777Labels = mixedMoment B raw5777step0 raw5777step0Labels := by
      have hz : ∀ j, raw5777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5777step0 = (fun i j => raw5777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5777step0 raw5777; decide +kernel
      have hl : raw5777step0Labels = raw5777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5777 raw5777Labels permutation434 hz
    mixedMoment B raw5777step0 raw5777step0Labels = mixedMoment B raw5777step1 raw5777step1Labels := by
      have ha : raw5777step1 = (fun i j => raw5777step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5777step1 raw5777step0; decide +kernel
      have hl : raw5777step1Labels = raw5777step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5777step0 raw5777step0Labels permutation38 permutation2
    _ = mixedMoment B node5165 node5165Labels := by rfl

def raw5778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5778 raw5778Labels = mixedMoment B node5165 node5165Labels := by
  calc
    mixedMoment B raw5778 raw5778Labels = mixedMoment B raw5778step0 raw5778step0Labels := by
      have hz : ∀ j, raw5778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5778step0 = (fun i j => raw5778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5778step0 raw5778; decide +kernel
      have hl : raw5778step0Labels = raw5778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5778 raw5778Labels permutation346 hz
    mixedMoment B raw5778step0 raw5778step0Labels = mixedMoment B raw5778step1 raw5778step1Labels := by
      have ha : raw5778step1 = (fun i j => raw5778step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5778step1 raw5778step0; decide +kernel
      have hl : raw5778step1Labels = raw5778step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5778step0 raw5778step0Labels permutation38 permutation2
    _ = mixedMoment B node5165 node5165Labels := by rfl

def raw5779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw5779step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5779step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5779step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5779step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5779step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5779 raw5779Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw5779 raw5779Labels = mixedMoment B raw5779step0 raw5779step0Labels := by
      have hz : ∀ j, raw5779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5779step0 = (fun i j => raw5779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5779step0 raw5779; decide +kernel
      have hl : raw5779step0Labels = raw5779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5779 raw5779Labels permutation434 hz
    mixedMoment B raw5779step0 raw5779step0Labels = mixedMoment B raw5779step1 raw5779step1Labels := by
      have hz : ∀ j, raw5779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5779step1 = (fun i j => raw5779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5779step1 raw5779step0; decide +kernel
      have hl : raw5779step1Labels = raw5779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5779step0 raw5779step0Labels permutation80 hz
    mixedMoment B raw5779step1 raw5779step1Labels = mixedMoment B raw5779step2 raw5779step2Labels := by
      have ha : raw5779step2 = (fun i j => raw5779step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5779step2 raw5779step1; decide +kernel
      have hl : raw5779step2Labels = raw5779step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5779step1 raw5779step1Labels permutation21 permutation4
    mixedMoment B raw5779step2 raw5779step2Labels = mixedMoment B raw5779step3 raw5779step3Labels := by
      have ha : raw5779step3 = -raw5779step2 := by apply Matrix.ext; change ∀ i j, raw5779step3 i j = -(raw5779step2 i j); unfold raw5779step3 raw5779step2; decide +kernel
      have hl : raw5779step3Labels = raw5779step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5779step3 raw5779step3Labels = mixedMoment B raw5779step4 raw5779step4Labels := by
      have ha : raw5779step4 = raw5779step3 := by apply Matrix.ext; unfold raw5779step4 raw5779step3; decide +kernel
      have hl : raw5779step3Labels = labelEmbedding7 ∘ raw5779step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5779step3 raw5779step3Labels raw5779step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4884 node4884Labels := by rfl

def raw5780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5780step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5780step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5780 raw5780Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw5780 raw5780Labels = mixedMoment B raw5780step0 raw5780step0Labels := by
      have hz : ∀ j, raw5780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5780step0 = (fun i j => raw5780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5780step0 raw5780; decide +kernel
      have hl : raw5780step0Labels = raw5780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5780 raw5780Labels permutation434 hz
    mixedMoment B raw5780step0 raw5780step0Labels = mixedMoment B raw5780step1 raw5780step1Labels := by
      have hz : ∀ j, raw5780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5780step1 = (fun i j => raw5780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5780step1 raw5780step0; decide +kernel
      have hl : raw5780step1Labels = raw5780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5780step0 raw5780step0Labels permutation80 hz
    mixedMoment B raw5780step1 raw5780step1Labels = mixedMoment B raw5780step2 raw5780step2Labels := by
      have ha : raw5780step2 = (fun i j => raw5780step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5780step2 raw5780step1; decide +kernel
      have hl : raw5780step2Labels = raw5780step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5780step1 raw5780step1Labels permutation25 permutation6
    mixedMoment B raw5780step2 raw5780step2Labels = mixedMoment B raw5780step3 raw5780step3Labels := by
      have ha : raw5780step3 = raw5780step2 := by apply Matrix.ext; unfold raw5780step3 raw5780step2; decide +kernel
      have hl : raw5780step2Labels = labelEmbedding9 ∘ raw5780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5780step2 raw5780step2Labels raw5780step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw5781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5781 raw5781Labels = mixedMoment B node4604 node4604Labels := by
  calc
    mixedMoment B raw5781 raw5781Labels = mixedMoment B raw5781step0 raw5781step0Labels := by
      have hz : ∀ j, raw5781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5781step0 = (fun i j => raw5781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5781step0 raw5781; decide +kernel
      have hl : raw5781step0Labels = raw5781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5781 raw5781Labels permutation434 hz
    _ = mixedMoment B node4604 node4604Labels := by rfl

def raw5782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5782 raw5782Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw5782 raw5782Labels = mixedMoment B raw5782step0 raw5782step0Labels := by
      have hz : ∀ j, raw5782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5782step0 = (fun i j => raw5782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5782step0 raw5782; decide +kernel
      have hl : raw5782step0Labels = raw5782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5782 raw5782Labels permutation434 hz
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw5783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5783 raw5783Labels = mixedMoment B node5136 node5136Labels := by
  calc
    mixedMoment B raw5783 raw5783Labels = mixedMoment B raw5783step0 raw5783step0Labels := by
      have ha : raw5783step0 = (fun i j => raw5783 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5783step0 raw5783; decide +kernel
      have hl : raw5783step0Labels = raw5783Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5783 raw5783Labels permutation200 permutation2
    _ = mixedMoment B node5136 node5136Labels := by rfl

def raw5784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw5784step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5784step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5784step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5784 raw5784Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw5784 raw5784Labels = mixedMoment B raw5784step0 raw5784step0Labels := by
      have hz : ∀ j, raw5784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5784step0 = (fun i j => raw5784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5784step0 raw5784; decide +kernel
      have hl : raw5784step0Labels = raw5784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5784 raw5784Labels permutation434 hz
    mixedMoment B raw5784step0 raw5784step0Labels = mixedMoment B raw5784step1 raw5784step1Labels := by
      have ha : raw5784step1 = (fun i j => raw5784step0 (permutation106 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5784step1 raw5784step0; decide +kernel
      have hl : raw5784step1Labels = raw5784step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5784step0 raw5784step0Labels permutation106 permutation4
    mixedMoment B raw5784step1 raw5784step1Labels = mixedMoment B raw5784step2 raw5784step2Labels := by
      have ha : raw5784step2 = -raw5784step1 := by apply Matrix.ext; change ∀ i j, raw5784step2 i j = -(raw5784step1 i j); unfold raw5784step2 raw5784step1; decide +kernel
      have hl : raw5784step2Labels = raw5784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5784step2 raw5784step2Labels = mixedMoment B raw5784step3 raw5784step3Labels := by
      have ha : raw5784step3 = raw5784step2 := by apply Matrix.ext; unfold raw5784step3 raw5784step2; decide +kernel
      have hl : raw5784step2Labels = labelEmbedding7 ∘ raw5784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5784step2 raw5784step2Labels raw5784step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw5785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5785 raw5785Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw5785 raw5785Labels = mixedMoment B raw5785step0 raw5785step0Labels := by
      have hz : ∀ j, raw5785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5785step0 = (fun i j => raw5785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5785step0 raw5785; decide +kernel
      have hl : raw5785step0Labels = raw5785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5785 raw5785Labels permutation434 hz
    mixedMoment B raw5785step0 raw5785step0Labels = mixedMoment B raw5785step1 raw5785step1Labels := by
      have ha : raw5785step1 = (fun i j => raw5785step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5785step1 raw5785step0; decide +kernel
      have hl : raw5785step1Labels = raw5785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5785step0 raw5785step0Labels permutation33 permutation2
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw5786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5786 raw5786Labels = mixedMoment B node4604 node4604Labels := by
  calc
    mixedMoment B raw5786 raw5786Labels = mixedMoment B raw5786step0 raw5786step0Labels := by
      have hz : ∀ j, raw5786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5786step0 = (fun i j => raw5786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5786step0 raw5786; decide +kernel
      have hl : raw5786step0Labels = raw5786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5786 raw5786Labels permutation346 hz
    _ = mixedMoment B node4604 node4604Labels := by rfl

def raw5787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5787 raw5787Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw5787 raw5787Labels = mixedMoment B raw5787step0 raw5787step0Labels := by
      have hz : ∀ j, raw5787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5787step0 = (fun i j => raw5787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5787step0 raw5787; decide +kernel
      have hl : raw5787step0Labels = raw5787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5787 raw5787Labels permutation346 hz
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw5788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5788 raw5788Labels = mixedMoment B node5136 node5136Labels := by
  calc
    mixedMoment B raw5788 raw5788Labels = mixedMoment B raw5788step0 raw5788step0Labels := by
      have ha : raw5788step0 = (fun i j => raw5788 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5788step0 raw5788; decide +kernel
      have hl : raw5788step0Labels = raw5788Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5788 raw5788Labels permutation176 permutation2
    _ = mixedMoment B node5136 node5136Labels := by rfl

def raw5789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw5789step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5789step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5789step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5789step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5789 raw5789Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw5789 raw5789Labels = mixedMoment B raw5789step0 raw5789step0Labels := by
      have hz : ∀ j, raw5789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5789step0 = (fun i j => raw5789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5789step0 raw5789; decide +kernel
      have hl : raw5789step0Labels = raw5789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5789 raw5789Labels permutation346 hz
    mixedMoment B raw5789step0 raw5789step0Labels = mixedMoment B raw5789step1 raw5789step1Labels := by
      have ha : raw5789step1 = (fun i j => raw5789step0 (permutation106 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5789step1 raw5789step0; decide +kernel
      have hl : raw5789step1Labels = raw5789step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5789step0 raw5789step0Labels permutation106 permutation4
    mixedMoment B raw5789step1 raw5789step1Labels = mixedMoment B raw5789step2 raw5789step2Labels := by
      have ha : raw5789step2 = -raw5789step1 := by apply Matrix.ext; change ∀ i j, raw5789step2 i j = -(raw5789step1 i j); unfold raw5789step2 raw5789step1; decide +kernel
      have hl : raw5789step2Labels = raw5789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5789step2 raw5789step2Labels = mixedMoment B raw5789step3 raw5789step3Labels := by
      have ha : raw5789step3 = raw5789step2 := by apply Matrix.ext; unfold raw5789step3 raw5789step2; decide +kernel
      have hl : raw5789step2Labels = labelEmbedding7 ∘ raw5789step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5789step2 raw5789step2Labels raw5789step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw5790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5790 raw5790Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw5790 raw5790Labels = mixedMoment B raw5790step0 raw5790step0Labels := by
      have hz : ∀ j, raw5790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5790step0 = (fun i j => raw5790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5790step0 raw5790; decide +kernel
      have hl : raw5790step0Labels = raw5790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5790 raw5790Labels permutation346 hz
    mixedMoment B raw5790step0 raw5790step0Labels = mixedMoment B raw5790step1 raw5790step1Labels := by
      have ha : raw5790step1 = (fun i j => raw5790step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5790step1 raw5790step0; decide +kernel
      have hl : raw5790step1Labels = raw5790step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5790step0 raw5790step0Labels permutation33 permutation2
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw5791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5791 raw5791Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw5791 raw5791Labels = mixedMoment B raw5791step0 raw5791step0Labels := by
      have hz : ∀ j, raw5791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5791step0 = (fun i j => raw5791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5791step0 raw5791; decide +kernel
      have hl : raw5791step0Labels = raw5791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5791 raw5791Labels permutation434 hz
    mixedMoment B raw5791step0 raw5791step0Labels = mixedMoment B raw5791step1 raw5791step1Labels := by
      have hz : ∀ j, raw5791step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5791step1 = (fun i j => raw5791step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5791step1 raw5791step0; decide +kernel
      have hl : raw5791step1Labels = raw5791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5791step0 raw5791step0Labels permutation80 hz
    mixedMoment B raw5791step1 raw5791step1Labels = mixedMoment B raw5791step2 raw5791step2Labels := by
      have ha : raw5791step2 = (fun i j => raw5791step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5791step2 raw5791step1; decide +kernel
      have hl : raw5791step2Labels = raw5791step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5791step1 raw5791step1Labels permutation9 permutation2
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw5792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5792step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5792step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5792 raw5792Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw5792 raw5792Labels = mixedMoment B raw5792step0 raw5792step0Labels := by
      have hz : ∀ j, raw5792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5792step0 = (fun i j => raw5792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5792step0 raw5792; decide +kernel
      have hl : raw5792step0Labels = raw5792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5792 raw5792Labels permutation434 hz
    mixedMoment B raw5792step0 raw5792step0Labels = mixedMoment B raw5792step1 raw5792step1Labels := by
      have hz : ∀ j, raw5792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5792step1 = (fun i j => raw5792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5792step1 raw5792step0; decide +kernel
      have hl : raw5792step1Labels = raw5792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5792step0 raw5792step0Labels permutation80 hz
    mixedMoment B raw5792step1 raw5792step1Labels = mixedMoment B raw5792step2 raw5792step2Labels := by
      have ha : raw5792step2 = (fun i j => raw5792step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5792step2 raw5792step1; decide +kernel
      have hl : raw5792step2Labels = raw5792step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5792step1 raw5792step1Labels permutation9 permutation2
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw5793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5793 raw5793Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw5793 raw5793Labels = mixedMoment B raw5793step0 raw5793step0Labels := by
      have hz : ∀ j, raw5793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5793step0 = (fun i j => raw5793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5793step0 raw5793; decide +kernel
      have hl : raw5793step0Labels = raw5793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5793 raw5793Labels permutation434 hz
    mixedMoment B raw5793step0 raw5793step0Labels = mixedMoment B raw5793step1 raw5793step1Labels := by
      have ha : raw5793step1 = (fun i j => raw5793step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5793step1 raw5793step0; decide +kernel
      have hl : raw5793step1Labels = raw5793step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5793step0 raw5793step0Labels permutation39 permutation2
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw5794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5794 raw5794Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw5794 raw5794Labels = mixedMoment B raw5794step0 raw5794step0Labels := by
      have hz : ∀ j, raw5794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5794step0 = (fun i j => raw5794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5794step0 raw5794; decide +kernel
      have hl : raw5794step0Labels = raw5794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5794 raw5794Labels permutation346 hz
    mixedMoment B raw5794step0 raw5794step0Labels = mixedMoment B raw5794step1 raw5794step1Labels := by
      have ha : raw5794step1 = (fun i j => raw5794step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5794step1 raw5794step0; decide +kernel
      have hl : raw5794step1Labels = raw5794step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5794step0 raw5794step0Labels permutation39 permutation2
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw5795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw5795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5795 raw5795Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5795 raw5795Labels = mixedMoment B raw5795step0 raw5795step0Labels := by
      have hz : ∀ j, raw5795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5795step0 = (fun i j => raw5795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5795step0 raw5795; decide +kernel
      have hl : raw5795step0Labels = raw5795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5795 raw5795Labels permutation434 hz
    mixedMoment B raw5795step0 raw5795step0Labels = mixedMoment B raw5795step1 raw5795step1Labels := by
      have hz : ∀ j, raw5795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5795step1 = (fun i j => raw5795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5795step1 raw5795step0; decide +kernel
      have hl : raw5795step1Labels = raw5795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5795step0 raw5795step0Labels permutation80 hz
    mixedMoment B raw5795step1 raw5795step1Labels = mixedMoment B raw5795step2 raw5795step2Labels := by
      have ha : raw5795step2 = (fun i j => raw5795step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5795step2 raw5795step1; decide +kernel
      have hl : raw5795step2Labels = raw5795step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5795step1 raw5795step1Labels permutation9 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw5796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5796 raw5796Labels = mixedMoment B node4610 node4610Labels := by
  calc
    mixedMoment B raw5796 raw5796Labels = mixedMoment B raw5796step0 raw5796step0Labels := by
      have hz : ∀ j, raw5796 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5796step0 = (fun i j => raw5796 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5796step0 raw5796; decide +kernel
      have hl : raw5796step0Labels = raw5796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5796 raw5796Labels permutation434 hz
    mixedMoment B raw5796step0 raw5796step0Labels = mixedMoment B raw5796step1 raw5796step1Labels := by
      have hz : ∀ j, raw5796step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5796step1 = (fun i j => raw5796step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5796step1 raw5796step0; decide +kernel
      have hl : raw5796step1Labels = raw5796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5796step0 raw5796step0Labels permutation80 hz
    _ = mixedMoment B node4610 node4610Labels := by rfl

def raw5797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw5797step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5797step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5797step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5797step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5797step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5797 raw5797Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw5797 raw5797Labels = mixedMoment B raw5797step0 raw5797step0Labels := by
      have hz : ∀ j, raw5797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5797step0 = (fun i j => raw5797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5797step0 raw5797; decide +kernel
      have hl : raw5797step0Labels = raw5797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5797 raw5797Labels permutation434 hz
    mixedMoment B raw5797step0 raw5797step0Labels = mixedMoment B raw5797step1 raw5797step1Labels := by
      have hz : ∀ j, raw5797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5797step1 = (fun i j => raw5797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5797step1 raw5797step0; decide +kernel
      have hl : raw5797step1Labels = raw5797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5797step0 raw5797step0Labels permutation80 hz
    mixedMoment B raw5797step1 raw5797step1Labels = mixedMoment B raw5797step2 raw5797step2Labels := by
      have ha : raw5797step2 = (fun i j => raw5797step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5797step2 raw5797step1; decide +kernel
      have hl : raw5797step2Labels = raw5797step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5797step1 raw5797step1Labels permutation31 permutation3
    mixedMoment B raw5797step2 raw5797step2Labels = mixedMoment B raw5797step3 raw5797step3Labels := by
      have ha : raw5797step3 = -raw5797step2 := by apply Matrix.ext; change ∀ i j, raw5797step3 i j = -(raw5797step2 i j); unfold raw5797step3 raw5797step2; decide +kernel
      have hl : raw5797step3Labels = raw5797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5797step3 raw5797step3Labels = mixedMoment B raw5797step4 raw5797step4Labels := by
      have ha : raw5797step4 = raw5797step3 := by apply Matrix.ext; unfold raw5797step4 raw5797step3; decide +kernel
      have hl : raw5797step3Labels = labelEmbedding6 ∘ raw5797step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5797step3 raw5797step3Labels raw5797step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw5798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5798step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5798step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5798 raw5798Labels = mixedMoment B node4840 node4840Labels := by
  calc
    mixedMoment B raw5798 raw5798Labels = mixedMoment B raw5798step0 raw5798step0Labels := by
      have hz : ∀ j, raw5798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5798step0 = (fun i j => raw5798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5798step0 raw5798; decide +kernel
      have hl : raw5798step0Labels = raw5798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5798 raw5798Labels permutation434 hz
    mixedMoment B raw5798step0 raw5798step0Labels = mixedMoment B raw5798step1 raw5798step1Labels := by
      have ha : raw5798step1 = (fun i j => raw5798step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5798step1 raw5798step0; decide +kernel
      have hl : raw5798step1Labels = raw5798step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5798step0 raw5798step0Labels permutation136 permutation5
    mixedMoment B raw5798step1 raw5798step1Labels = mixedMoment B raw5798step2 raw5798step2Labels := by
      have ha : raw5798step2 = raw5798step1 := by apply Matrix.ext; unfold raw5798step2 raw5798step1; decide +kernel
      have hl : raw5798step1Labels = labelEmbedding8 ∘ raw5798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5798step1 raw5798step1Labels raw5798step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4840 node4840Labels := by rfl

def raw5799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5799step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5799 raw5799Labels = mixedMoment B node4840 node4840Labels := by
  calc
    mixedMoment B raw5799 raw5799Labels = mixedMoment B raw5799step0 raw5799step0Labels := by
      have hz : ∀ j, raw5799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5799step0 = (fun i j => raw5799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5799step0 raw5799; decide +kernel
      have hl : raw5799step0Labels = raw5799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5799 raw5799Labels permutation346 hz
    mixedMoment B raw5799step0 raw5799step0Labels = mixedMoment B raw5799step1 raw5799step1Labels := by
      have ha : raw5799step1 = (fun i j => raw5799step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5799step1 raw5799step0; decide +kernel
      have hl : raw5799step1Labels = raw5799step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5799step0 raw5799step0Labels permutation136 permutation5
    mixedMoment B raw5799step1 raw5799step1Labels = mixedMoment B raw5799step2 raw5799step2Labels := by
      have ha : raw5799step2 = raw5799step1 := by apply Matrix.ext; unfold raw5799step2 raw5799step1; decide +kernel
      have hl : raw5799step1Labels = labelEmbedding8 ∘ raw5799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5799step1 raw5799step1Labels raw5799step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4840 node4840Labels := by rfl

def raw5800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 3, -3], ![3, -3, 0]]
def raw5800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5800step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5800step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5800step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5800step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5800 raw5800Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw5800 raw5800Labels = mixedMoment B raw5800step0 raw5800step0Labels := by
      have hz : ∀ j, raw5800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5800step0 = (fun i j => raw5800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5800step0 raw5800; decide +kernel
      have hl : raw5800step0Labels = raw5800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5800 raw5800Labels permutation434 hz
    mixedMoment B raw5800step0 raw5800step0Labels = mixedMoment B raw5800step1 raw5800step1Labels := by
      have hz : ∀ j, raw5800step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5800step1 = (fun i j => raw5800step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5800step1 raw5800step0; decide +kernel
      have hl : raw5800step1Labels = raw5800step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5800step0 raw5800step0Labels permutation80 hz
    mixedMoment B raw5800step1 raw5800step1Labels = mixedMoment B raw5800step2 raw5800step2Labels := by
      have ha : raw5800step2 = (fun i j => raw5800step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5800step2 raw5800step1; decide +kernel
      have hl : raw5800step2Labels = raw5800step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5800step1 raw5800step1Labels permutation28 permutation5
    mixedMoment B raw5800step2 raw5800step2Labels = mixedMoment B raw5800step3 raw5800step3Labels := by
      have ha : raw5800step3 = raw5800step2 := by apply Matrix.ext; unfold raw5800step3 raw5800step2; decide +kernel
      have hl : raw5800step2Labels = labelEmbedding8 ∘ raw5800step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5800step2 raw5800step2Labels raw5800step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw5801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5801step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5801 raw5801Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw5801 raw5801Labels = mixedMoment B raw5801step0 raw5801step0Labels := by
      have hz : ∀ j, raw5801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5801step0 = (fun i j => raw5801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5801step0 raw5801; decide +kernel
      have hl : raw5801step0Labels = raw5801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5801 raw5801Labels permutation434 hz
    mixedMoment B raw5801step0 raw5801step0Labels = mixedMoment B raw5801step1 raw5801step1Labels := by
      have hz : ∀ j, raw5801step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5801step1 = (fun i j => raw5801step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5801step1 raw5801step0; decide +kernel
      have hl : raw5801step1Labels = raw5801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5801step0 raw5801step0Labels permutation80 hz
    mixedMoment B raw5801step1 raw5801step1Labels = mixedMoment B raw5801step2 raw5801step2Labels := by
      have ha : raw5801step2 = (fun i j => raw5801step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5801step2 raw5801step1; decide +kernel
      have hl : raw5801step2Labels = raw5801step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5801step1 raw5801step1Labels permutation25 permutation6
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw5802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5802 raw5802Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw5802 raw5802Labels = mixedMoment B raw5802step0 raw5802step0Labels := by
      have hz : ∀ j, raw5802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5802step0 = (fun i j => raw5802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5802step0 raw5802; decide +kernel
      have hl : raw5802step0Labels = raw5802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5802 raw5802Labels permutation434 hz
    mixedMoment B raw5802step0 raw5802step0Labels = mixedMoment B raw5802step1 raw5802step1Labels := by
      have ha : raw5802step1 = (fun i j => raw5802step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5802step1 raw5802step0; decide +kernel
      have hl : raw5802step1Labels = raw5802step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5802step0 raw5802step0Labels permutation121 permutation6
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw5803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5803step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5803 raw5803Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw5803 raw5803Labels = mixedMoment B raw5803step0 raw5803step0Labels := by
      have hz : ∀ j, raw5803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5803step0 = (fun i j => raw5803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5803step0 raw5803; decide +kernel
      have hl : raw5803step0Labels = raw5803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5803 raw5803Labels permutation346 hz
    mixedMoment B raw5803step0 raw5803step0Labels = mixedMoment B raw5803step1 raw5803step1Labels := by
      have ha : raw5803step1 = (fun i j => raw5803step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5803step1 raw5803step0; decide +kernel
      have hl : raw5803step1Labels = raw5803step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5803step0 raw5803step0Labels permutation121 permutation6
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw5804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5804step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5804 raw5804Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw5804 raw5804Labels = mixedMoment B raw5804step0 raw5804step0Labels := by
      have hz : ∀ j, raw5804 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5804step0 = (fun i j => raw5804 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5804step0 raw5804; decide +kernel
      have hl : raw5804step0Labels = raw5804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5804 raw5804Labels permutation434 hz
    mixedMoment B raw5804step0 raw5804step0Labels = mixedMoment B raw5804step1 raw5804step1Labels := by
      have hz : ∀ j, raw5804step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5804step1 = (fun i j => raw5804step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5804step1 raw5804step0; decide +kernel
      have hl : raw5804step1Labels = raw5804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5804step0 raw5804step0Labels permutation80 hz
    mixedMoment B raw5804step1 raw5804step1Labels = mixedMoment B raw5804step2 raw5804step2Labels := by
      have ha : raw5804step2 = (fun i j => raw5804step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5804step2 raw5804step1; decide +kernel
      have hl : raw5804step2Labels = raw5804step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5804step1 raw5804step1Labels permutation25 permutation6
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw5805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5805step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5805 raw5805Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw5805 raw5805Labels = mixedMoment B raw5805step0 raw5805step0Labels := by
      have hz : ∀ j, raw5805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5805step0 = (fun i j => raw5805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5805step0 raw5805; decide +kernel
      have hl : raw5805step0Labels = raw5805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5805 raw5805Labels permutation434 hz
    mixedMoment B raw5805step0 raw5805step0Labels = mixedMoment B raw5805step1 raw5805step1Labels := by
      have hz : ∀ j, raw5805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5805step1 = (fun i j => raw5805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5805step1 raw5805step0; decide +kernel
      have hl : raw5805step1Labels = raw5805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5805step0 raw5805step0Labels permutation80 hz
    mixedMoment B raw5805step1 raw5805step1Labels = mixedMoment B raw5805step2 raw5805step2Labels := by
      have ha : raw5805step2 = (fun i j => raw5805step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5805step2 raw5805step1; decide +kernel
      have hl : raw5805step2Labels = raw5805step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5805step1 raw5805step1Labels permutation25 permutation6
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw5806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5806step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw5806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5806 raw5806Labels = mixedMoment B node1288 node1288Labels := by
  calc
    mixedMoment B raw5806 raw5806Labels = mixedMoment B raw5806step0 raw5806step0Labels := by
      have hz : ∀ j, raw5806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5806step0 = (fun i j => raw5806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5806step0 raw5806; decide +kernel
      have hl : raw5806step0Labels = raw5806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5806 raw5806Labels permutation434 hz
    mixedMoment B raw5806step0 raw5806step0Labels = mixedMoment B raw5806step1 raw5806step1Labels := by
      have hz : ∀ j, raw5806step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5806step1 = (fun i j => raw5806step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5806step1 raw5806step0; decide +kernel
      have hl : raw5806step1Labels = raw5806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5806step0 raw5806step0Labels permutation80 hz
    mixedMoment B raw5806step1 raw5806step1Labels = mixedMoment B raw5806step2 raw5806step2Labels := by
      have ha : raw5806step2 = (fun i j => raw5806step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5806step2 raw5806step1; decide +kernel
      have hl : raw5806step2Labels = raw5806step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5806step1 raw5806step1Labels permutation10 permutation3
    _ = mixedMoment B node1288 node1288Labels := by rfl

def raw5807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw5807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5807 raw5807Labels = mixedMoment B node2733 node2733Labels := by
  calc
    mixedMoment B raw5807 raw5807Labels = mixedMoment B raw5807step0 raw5807step0Labels := by
      have hz : ∀ j, raw5807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5807step0 = (fun i j => raw5807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5807step0 raw5807; decide +kernel
      have hl : raw5807step0Labels = raw5807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5807 raw5807Labels permutation434 hz
    mixedMoment B raw5807step0 raw5807step0Labels = mixedMoment B raw5807step1 raw5807step1Labels := by
      have ha : raw5807step1 = (fun i j => raw5807step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5807step1 raw5807step0; decide +kernel
      have hl : raw5807step1Labels = raw5807step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5807step0 raw5807step0Labels permutation121 permutation6
    _ = mixedMoment B node2733 node2733Labels := by rfl

def raw5808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5808step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw5808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5808 raw5808Labels = mixedMoment B node2733 node2733Labels := by
  calc
    mixedMoment B raw5808 raw5808Labels = mixedMoment B raw5808step0 raw5808step0Labels := by
      have hz : ∀ j, raw5808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5808step0 = (fun i j => raw5808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5808step0 raw5808; decide +kernel
      have hl : raw5808step0Labels = raw5808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5808 raw5808Labels permutation346 hz
    mixedMoment B raw5808step0 raw5808step0Labels = mixedMoment B raw5808step1 raw5808step1Labels := by
      have ha : raw5808step1 = (fun i j => raw5808step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5808step1 raw5808step0; decide +kernel
      have hl : raw5808step1Labels = raw5808step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5808step0 raw5808step0Labels permutation121 permutation6
    _ = mixedMoment B node2733 node2733Labels := by rfl

def raw5809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5809step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw5809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5809 raw5809Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw5809 raw5809Labels = mixedMoment B raw5809step0 raw5809step0Labels := by
      have hz : ∀ j, raw5809 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5809step0 = (fun i j => raw5809 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5809step0 raw5809; decide +kernel
      have hl : raw5809step0Labels = raw5809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5809 raw5809Labels permutation434 hz
    mixedMoment B raw5809step0 raw5809step0Labels = mixedMoment B raw5809step1 raw5809step1Labels := by
      have hz : ∀ j, raw5809step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5809step1 = (fun i j => raw5809step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5809step1 raw5809step0; decide +kernel
      have hl : raw5809step1Labels = raw5809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5809step0 raw5809step0Labels permutation80 hz
    mixedMoment B raw5809step1 raw5809step1Labels = mixedMoment B raw5809step2 raw5809step2Labels := by
      have ha : raw5809step2 = (fun i j => raw5809step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5809step2 raw5809step1; decide +kernel
      have hl : raw5809step2Labels = raw5809step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5809step1 raw5809step1Labels permutation25 permutation6
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw5810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5810 raw5810Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw5810 raw5810Labels = mixedMoment B raw5810step0 raw5810step0Labels := by
      have hz : ∀ j, raw5810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5810step0 = (fun i j => raw5810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5810step0 raw5810; decide +kernel
      have hl : raw5810step0Labels = raw5810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5810 raw5810Labels permutation434 hz
    mixedMoment B raw5810step0 raw5810step0Labels = mixedMoment B raw5810step1 raw5810step1Labels := by
      have hz : ∀ j, raw5810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5810step1 = (fun i j => raw5810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5810step1 raw5810step0; decide +kernel
      have hl : raw5810step1Labels = raw5810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5810step0 raw5810step0Labels permutation80 hz
    mixedMoment B raw5810step1 raw5810step1Labels = mixedMoment B raw5810step2 raw5810step2Labels := by
      have ha : raw5810step2 = (fun i j => raw5810step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5810step2 raw5810step1; decide +kernel
      have hl : raw5810step2Labels = raw5810step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5810step1 raw5810step1Labels permutation25 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw5811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5811step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5811 raw5811Labels = mixedMoment B node1257 node1257Labels := by
  calc
    mixedMoment B raw5811 raw5811Labels = mixedMoment B raw5811step0 raw5811step0Labels := by
      have hz : ∀ j, raw5811 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5811step0 = (fun i j => raw5811 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5811step0 raw5811; decide +kernel
      have hl : raw5811step0Labels = raw5811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5811 raw5811Labels permutation434 hz
    mixedMoment B raw5811step0 raw5811step0Labels = mixedMoment B raw5811step1 raw5811step1Labels := by
      have ha : raw5811step1 = (fun i j => raw5811step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5811step1 raw5811step0; decide +kernel
      have hl : raw5811step1Labels = raw5811step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5811step0 raw5811step0Labels permutation34 permutation3
    _ = mixedMoment B node1257 node1257Labels := by rfl

def raw5812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5812 raw5812Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw5812 raw5812Labels = mixedMoment B raw5812step0 raw5812step0Labels := by
      have hz : ∀ j, raw5812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5812step0 = (fun i j => raw5812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5812step0 raw5812; decide +kernel
      have hl : raw5812step0Labels = raw5812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5812 raw5812Labels permutation434 hz
    mixedMoment B raw5812step0 raw5812step0Labels = mixedMoment B raw5812step1 raw5812step1Labels := by
      have ha : raw5812step1 = (fun i j => raw5812step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5812step1 raw5812step0; decide +kernel
      have hl : raw5812step1Labels = raw5812step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5812step0 raw5812step0Labels permutation121 permutation6
    _ = mixedMoment B node2759 node2759Labels := by rfl

def raw5813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw5813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5813 raw5813Labels = mixedMoment B node2715 node2715Labels := by
  calc
    mixedMoment B raw5813 raw5813Labels = mixedMoment B raw5813step0 raw5813step0Labels := by
      have ha : raw5813step0 = (fun i j => raw5813 (permutation562 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5813step0 raw5813; decide +kernel
      have hl : raw5813step0Labels = raw5813Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5813 raw5813Labels permutation562 permutation6
    _ = mixedMoment B node2715 node2715Labels := by rfl

def raw5814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw5814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5814 raw5814Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw5814 raw5814Labels = mixedMoment B raw5814step0 raw5814step0Labels := by
      have hz : ∀ j, raw5814 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5814step0 = (fun i j => raw5814 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5814step0 raw5814; decide +kernel
      have hl : raw5814step0Labels = raw5814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5814 raw5814Labels permutation434 hz
    mixedMoment B raw5814step0 raw5814step0Labels = mixedMoment B raw5814step1 raw5814step1Labels := by
      have ha : raw5814step1 = (fun i j => raw5814step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5814step1 raw5814step0; decide +kernel
      have hl : raw5814step1Labels = raw5814step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5814step0 raw5814step0Labels permutation121 permutation6
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw5815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw5815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5815 raw5815Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw5815 raw5815Labels = mixedMoment B raw5815step0 raw5815step0Labels := by
      have hz : ∀ j, raw5815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5815step0 = (fun i j => raw5815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5815step0 raw5815; decide +kernel
      have hl : raw5815step0Labels = raw5815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5815 raw5815Labels permutation434 hz
    mixedMoment B raw5815step0 raw5815step0Labels = mixedMoment B raw5815step1 raw5815step1Labels := by
      have ha : raw5815step1 = (fun i j => raw5815step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5815step1 raw5815step0; decide +kernel
      have hl : raw5815step1Labels = raw5815step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5815step0 raw5815step0Labels permutation121 permutation6
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw5816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5816step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5816 raw5816Labels = mixedMoment B node1257 node1257Labels := by
  calc
    mixedMoment B raw5816 raw5816Labels = mixedMoment B raw5816step0 raw5816step0Labels := by
      have hz : ∀ j, raw5816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5816step0 = (fun i j => raw5816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5816step0 raw5816; decide +kernel
      have hl : raw5816step0Labels = raw5816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5816 raw5816Labels permutation346 hz
    mixedMoment B raw5816step0 raw5816step0Labels = mixedMoment B raw5816step1 raw5816step1Labels := by
      have ha : raw5816step1 = (fun i j => raw5816step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5816step1 raw5816step0; decide +kernel
      have hl : raw5816step1Labels = raw5816step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5816step0 raw5816step0Labels permutation34 permutation3
    _ = mixedMoment B node1257 node1257Labels := by rfl

def raw5817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5817step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5817 raw5817Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw5817 raw5817Labels = mixedMoment B raw5817step0 raw5817step0Labels := by
      have hz : ∀ j, raw5817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5817step0 = (fun i j => raw5817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5817step0 raw5817; decide +kernel
      have hl : raw5817step0Labels = raw5817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5817 raw5817Labels permutation346 hz
    mixedMoment B raw5817step0 raw5817step0Labels = mixedMoment B raw5817step1 raw5817step1Labels := by
      have ha : raw5817step1 = (fun i j => raw5817step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5817step1 raw5817step0; decide +kernel
      have hl : raw5817step1Labels = raw5817step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5817step0 raw5817step0Labels permutation121 permutation6
    _ = mixedMoment B node2759 node2759Labels := by rfl

def raw5818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw5818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5818 raw5818Labels = mixedMoment B node2715 node2715Labels := by
  calc
    mixedMoment B raw5818 raw5818Labels = mixedMoment B raw5818step0 raw5818step0Labels := by
      have ha : raw5818step0 = (fun i j => raw5818 (permutation546 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5818step0 raw5818; decide +kernel
      have hl : raw5818step0Labels = raw5818Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5818 raw5818Labels permutation546 permutation6
    _ = mixedMoment B node2715 node2715Labels := by rfl

def raw5819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5819step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw5819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5819 raw5819Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw5819 raw5819Labels = mixedMoment B raw5819step0 raw5819step0Labels := by
      have hz : ∀ j, raw5819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5819step0 = (fun i j => raw5819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5819step0 raw5819; decide +kernel
      have hl : raw5819step0Labels = raw5819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5819 raw5819Labels permutation346 hz
    mixedMoment B raw5819step0 raw5819step0Labels = mixedMoment B raw5819step1 raw5819step1Labels := by
      have ha : raw5819step1 = (fun i j => raw5819step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5819step1 raw5819step0; decide +kernel
      have hl : raw5819step1Labels = raw5819step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5819step0 raw5819step0Labels permutation121 permutation6
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw5820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5820step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw5820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5820 raw5820Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw5820 raw5820Labels = mixedMoment B raw5820step0 raw5820step0Labels := by
      have hz : ∀ j, raw5820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5820step0 = (fun i j => raw5820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5820step0 raw5820; decide +kernel
      have hl : raw5820step0Labels = raw5820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5820 raw5820Labels permutation346 hz
    mixedMoment B raw5820step0 raw5820step0Labels = mixedMoment B raw5820step1 raw5820step1Labels := by
      have ha : raw5820step1 = (fun i j => raw5820step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5820step1 raw5820step0; decide +kernel
      have hl : raw5820step1Labels = raw5820step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5820step0 raw5820step0Labels permutation121 permutation6
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw5821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5821step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5821step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw5821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5821 raw5821Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw5821 raw5821Labels = mixedMoment B raw5821step0 raw5821step0Labels := by
      have hz : ∀ j, raw5821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5821step0 = (fun i j => raw5821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5821step0 raw5821; decide +kernel
      have hl : raw5821step0Labels = raw5821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5821 raw5821Labels permutation434 hz
    mixedMoment B raw5821step0 raw5821step0Labels = mixedMoment B raw5821step1 raw5821step1Labels := by
      have hz : ∀ j, raw5821step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5821step1 = (fun i j => raw5821step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5821step1 raw5821step0; decide +kernel
      have hl : raw5821step1Labels = raw5821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5821step0 raw5821step0Labels permutation80 hz
    mixedMoment B raw5821step1 raw5821step1Labels = mixedMoment B raw5821step2 raw5821step2Labels := by
      have ha : raw5821step2 = (fun i j => raw5821step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5821step2 raw5821step1; decide +kernel
      have hl : raw5821step2Labels = raw5821step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5821step1 raw5821step1Labels permutation8 permutation3
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw5822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5822step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5822step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5822step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5822step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw5822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5822 raw5822Labels = mixedMoment B node3005 node3005Labels := by
  calc
    mixedMoment B raw5822 raw5822Labels = mixedMoment B raw5822step0 raw5822step0Labels := by
      have hz : ∀ j, raw5822 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5822step0 = (fun i j => raw5822 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5822step0 raw5822; decide +kernel
      have hl : raw5822step0Labels = raw5822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5822 raw5822Labels permutation434 hz
    mixedMoment B raw5822step0 raw5822step0Labels = mixedMoment B raw5822step1 raw5822step1Labels := by
      have hz : ∀ j, raw5822step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5822step1 = (fun i j => raw5822step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5822step1 raw5822step0; decide +kernel
      have hl : raw5822step1Labels = raw5822step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5822step0 raw5822step0Labels permutation80 hz
    mixedMoment B raw5822step1 raw5822step1Labels = mixedMoment B raw5822step2 raw5822step2Labels := by
      have ha : raw5822step2 = (fun i j => raw5822step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5822step2 raw5822step1; decide +kernel
      have hl : raw5822step2Labels = raw5822step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5822step1 raw5822step1Labels permutation8 permutation3
    _ = mixedMoment B node3005 node3005Labels := by rfl

def raw5823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5823step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw5823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5823 raw5823Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw5823 raw5823Labels = mixedMoment B raw5823step0 raw5823step0Labels := by
      have hz : ∀ j, raw5823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5823step0 = (fun i j => raw5823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5823step0 raw5823; decide +kernel
      have hl : raw5823step0Labels = raw5823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5823 raw5823Labels permutation434 hz
    mixedMoment B raw5823step0 raw5823step0Labels = mixedMoment B raw5823step1 raw5823step1Labels := by
      have ha : raw5823step1 = (fun i j => raw5823step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5823step1 raw5823step0; decide +kernel
      have hl : raw5823step1Labels = raw5823step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5823step0 raw5823step0Labels permutation38 permutation3
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw5824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw5824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5824 raw5824Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw5824 raw5824Labels = mixedMoment B raw5824step0 raw5824step0Labels := by
      have hz : ∀ j, raw5824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5824step0 = (fun i j => raw5824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5824step0 raw5824; decide +kernel
      have hl : raw5824step0Labels = raw5824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5824 raw5824Labels permutation346 hz
    mixedMoment B raw5824step0 raw5824step0Labels = mixedMoment B raw5824step1 raw5824step1Labels := by
      have ha : raw5824step1 = (fun i j => raw5824step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5824step1 raw5824step0; decide +kernel
      have hl : raw5824step1Labels = raw5824step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5824step0 raw5824step0Labels permutation38 permutation3
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw5825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5825step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw5825step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw5825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5825 raw5825Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw5825 raw5825Labels = mixedMoment B raw5825step0 raw5825step0Labels := by
      have hz : ∀ j, raw5825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5825step0 = (fun i j => raw5825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5825step0 raw5825; decide +kernel
      have hl : raw5825step0Labels = raw5825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5825 raw5825Labels permutation434 hz
    mixedMoment B raw5825step0 raw5825step0Labels = mixedMoment B raw5825step1 raw5825step1Labels := by
      have hz : ∀ j, raw5825step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5825step1 = (fun i j => raw5825step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5825step1 raw5825step0; decide +kernel
      have hl : raw5825step1Labels = raw5825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5825step0 raw5825step0Labels permutation80 hz
    mixedMoment B raw5825step1 raw5825step1Labels = mixedMoment B raw5825step2 raw5825step2Labels := by
      have ha : raw5825step2 = (fun i j => raw5825step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5825step2 raw5825step1; decide +kernel
      have hl : raw5825step2Labels = raw5825step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5825step1 raw5825step1Labels permutation9 permutation3
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw5826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5826step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5826step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw5826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5826 raw5826Labels = mixedMoment B node1258 node1258Labels := by
  calc
    mixedMoment B raw5826 raw5826Labels = mixedMoment B raw5826step0 raw5826step0Labels := by
      have hz : ∀ j, raw5826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5826step0 = (fun i j => raw5826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5826step0 raw5826; decide +kernel
      have hl : raw5826step0Labels = raw5826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5826 raw5826Labels permutation434 hz
    mixedMoment B raw5826step0 raw5826step0Labels = mixedMoment B raw5826step1 raw5826step1Labels := by
      have hz : ∀ j, raw5826step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5826step1 = (fun i j => raw5826step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5826step1 raw5826step0; decide +kernel
      have hl : raw5826step1Labels = raw5826step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5826step0 raw5826step0Labels permutation80 hz
    mixedMoment B raw5826step1 raw5826step1Labels = mixedMoment B raw5826step2 raw5826step2Labels := by
      have ha : raw5826step2 = (fun i j => raw5826step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5826step2 raw5826step1; decide +kernel
      have hl : raw5826step2Labels = raw5826step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5826step1 raw5826step1Labels permutation8 permutation3
    _ = mixedMoment B node1258 node1258Labels := by rfl

def raw5827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5827step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5827step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw5827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5827step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5827step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5827 raw5827Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw5827 raw5827Labels = mixedMoment B raw5827step0 raw5827step0Labels := by
      have hz : ∀ j, raw5827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5827step0 = (fun i j => raw5827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5827step0 raw5827; decide +kernel
      have hl : raw5827step0Labels = raw5827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5827 raw5827Labels permutation434 hz
    mixedMoment B raw5827step0 raw5827step0Labels = mixedMoment B raw5827step1 raw5827step1Labels := by
      have hz : ∀ j, raw5827step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5827step1 = (fun i j => raw5827step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5827step1 raw5827step0; decide +kernel
      have hl : raw5827step1Labels = raw5827step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5827step0 raw5827step0Labels permutation80 hz
    mixedMoment B raw5827step1 raw5827step1Labels = mixedMoment B raw5827step2 raw5827step2Labels := by
      have ha : raw5827step2 = (fun i j => raw5827step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5827step2 raw5827step1; decide +kernel
      have hl : raw5827step2Labels = raw5827step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5827step1 raw5827step1Labels permutation31 permutation3
    mixedMoment B raw5827step2 raw5827step2Labels = mixedMoment B raw5827step3 raw5827step3Labels := by
      have ha : raw5827step3 = -raw5827step2 := by apply Matrix.ext; change ∀ i j, raw5827step3 i j = -(raw5827step2 i j); unfold raw5827step3 raw5827step2; decide +kernel
      have hl : raw5827step3Labels = raw5827step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

def raw5828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5828step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw5828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw5828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5828 raw5828Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw5828 raw5828Labels = mixedMoment B raw5828step0 raw5828step0Labels := by
      have hz : ∀ j, raw5828 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5828step0 = (fun i j => raw5828 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5828step0 raw5828; decide +kernel
      have hl : raw5828step0Labels = raw5828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5828 raw5828Labels permutation434 hz
    mixedMoment B raw5828step0 raw5828step0Labels = mixedMoment B raw5828step1 raw5828step1Labels := by
      have ha : raw5828step1 = (fun i j => raw5828step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5828step1 raw5828step0; decide +kernel
      have hl : raw5828step1Labels = raw5828step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5828step0 raw5828step0Labels permutation149 permutation3
    mixedMoment B raw5828step1 raw5828step1Labels = mixedMoment B raw5828step2 raw5828step2Labels := by
      have ha : raw5828step2 = -raw5828step1 := by apply Matrix.ext; change ∀ i j, raw5828step2 i j = -(raw5828step1 i j); unfold raw5828step2 raw5828step1; decide +kernel
      have hl : raw5828step2Labels = raw5828step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2121 node2121Labels := by rfl

def raw5829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5829step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw5829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw5829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5829 raw5829Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw5829 raw5829Labels = mixedMoment B raw5829step0 raw5829step0Labels := by
      have hz : ∀ j, raw5829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5829step0 = (fun i j => raw5829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5829step0 raw5829; decide +kernel
      have hl : raw5829step0Labels = raw5829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5829 raw5829Labels permutation346 hz
    mixedMoment B raw5829step0 raw5829step0Labels = mixedMoment B raw5829step1 raw5829step1Labels := by
      have ha : raw5829step1 = (fun i j => raw5829step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5829step1 raw5829step0; decide +kernel
      have hl : raw5829step1Labels = raw5829step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5829step0 raw5829step0Labels permutation149 permutation3
    mixedMoment B raw5829step1 raw5829step1Labels = mixedMoment B raw5829step2 raw5829step2Labels := by
      have ha : raw5829step2 = -raw5829step1 := by apply Matrix.ext; change ∀ i j, raw5829step2 i j = -(raw5829step1 i j); unfold raw5829step2 raw5829step1; decide +kernel
      have hl : raw5829step2Labels = raw5829step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2121 node2121Labels := by rfl

def raw5830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 3, -3], ![3, -3, 0]]
def raw5830step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5830step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw5830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5830step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw5830step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5830 raw5830Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw5830 raw5830Labels = mixedMoment B raw5830step0 raw5830step0Labels := by
      have hz : ∀ j, raw5830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5830step0 = (fun i j => raw5830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5830step0 raw5830; decide +kernel
      have hl : raw5830step0Labels = raw5830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5830 raw5830Labels permutation434 hz
    mixedMoment B raw5830step0 raw5830step0Labels = mixedMoment B raw5830step1 raw5830step1Labels := by
      have hz : ∀ j, raw5830step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5830step1 = (fun i j => raw5830step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5830step1 raw5830step0; decide +kernel
      have hl : raw5830step1Labels = raw5830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5830step0 raw5830step0Labels permutation80 hz
    mixedMoment B raw5830step1 raw5830step1Labels = mixedMoment B raw5830step2 raw5830step2Labels := by
      have ha : raw5830step2 = (fun i j => raw5830step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5830step2 raw5830step1; decide +kernel
      have hl : raw5830step2Labels = raw5830step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5830step1 raw5830step1Labels permutation29 permutation3
    mixedMoment B raw5830step2 raw5830step2Labels = mixedMoment B raw5830step3 raw5830step3Labels := by
      have ha : raw5830step3 = -raw5830step2 := by apply Matrix.ext; change ∀ i j, raw5830step3 i j = -(raw5830step2 i j); unfold raw5830step3 raw5830step2; decide +kernel
      have hl : raw5830step3Labels = raw5830step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw5831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5831step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5831step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5831step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5831step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5831step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5831step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5831 raw5831Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw5831 raw5831Labels = mixedMoment B raw5831step0 raw5831step0Labels := by
      have hz : ∀ j, raw5831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5831step0 = (fun i j => raw5831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5831step0 raw5831; decide +kernel
      have hl : raw5831step0Labels = raw5831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5831 raw5831Labels permutation434 hz
    mixedMoment B raw5831step0 raw5831step0Labels = mixedMoment B raw5831step1 raw5831step1Labels := by
      have hz : ∀ j, raw5831step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5831step1 = (fun i j => raw5831step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5831step1 raw5831step0; decide +kernel
      have hl : raw5831step1Labels = raw5831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5831step0 raw5831step0Labels permutation80 hz
    mixedMoment B raw5831step1 raw5831step1Labels = mixedMoment B raw5831step2 raw5831step2Labels := by
      have ha : raw5831step2 = (fun i j => raw5831step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5831step2 raw5831step1; decide +kernel
      have hl : raw5831step2Labels = raw5831step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5831step1 raw5831step1Labels permutation25 permutation7
    mixedMoment B raw5831step2 raw5831step2Labels = mixedMoment B raw5831step3 raw5831step3Labels := by
      have ha : raw5831step3 = raw5831step2 := by apply Matrix.ext; unfold raw5831step3 raw5831step2; decide +kernel
      have hl : raw5831step2Labels = labelEmbedding1 ∘ raw5831step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5831step2 raw5831step2Labels raw5831step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw5832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5832step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5832 raw5832Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw5832 raw5832Labels = mixedMoment B raw5832step0 raw5832step0Labels := by
      have hz : ∀ j, raw5832 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5832step0 = (fun i j => raw5832 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5832step0 raw5832; decide +kernel
      have hl : raw5832step0Labels = raw5832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5832 raw5832Labels permutation434 hz
    mixedMoment B raw5832step0 raw5832step0Labels = mixedMoment B raw5832step1 raw5832step1Labels := by
      have ha : raw5832step1 = (fun i j => raw5832step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5832step1 raw5832step0; decide +kernel
      have hl : raw5832step1Labels = raw5832step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5832step0 raw5832step0Labels permutation127 permutation7
    mixedMoment B raw5832step1 raw5832step1Labels = mixedMoment B raw5832step2 raw5832step2Labels := by
      have ha : raw5832step2 = raw5832step1 := by apply Matrix.ext; unfold raw5832step2 raw5832step1; decide +kernel
      have hl : raw5832step1Labels = labelEmbedding1 ∘ raw5832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5832step1 raw5832step1Labels raw5832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw5833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5833step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5833 raw5833Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw5833 raw5833Labels = mixedMoment B raw5833step0 raw5833step0Labels := by
      have hz : ∀ j, raw5833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5833step0 = (fun i j => raw5833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5833step0 raw5833; decide +kernel
      have hl : raw5833step0Labels = raw5833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5833 raw5833Labels permutation346 hz
    mixedMoment B raw5833step0 raw5833step0Labels = mixedMoment B raw5833step1 raw5833step1Labels := by
      have ha : raw5833step1 = (fun i j => raw5833step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5833step1 raw5833step0; decide +kernel
      have hl : raw5833step1Labels = raw5833step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5833step0 raw5833step0Labels permutation127 permutation7
    mixedMoment B raw5833step1 raw5833step1Labels = mixedMoment B raw5833step2 raw5833step2Labels := by
      have ha : raw5833step2 = raw5833step1 := by apply Matrix.ext; unfold raw5833step2 raw5833step1; decide +kernel
      have hl : raw5833step1Labels = labelEmbedding1 ∘ raw5833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5833step1 raw5833step1Labels raw5833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw5834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5834step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5834step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw5834step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5834step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5834step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5834step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5834step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5834 raw5834Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw5834 raw5834Labels = mixedMoment B raw5834step0 raw5834step0Labels := by
      have hz : ∀ j, raw5834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5834step0 = (fun i j => raw5834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5834step0 raw5834; decide +kernel
      have hl : raw5834step0Labels = raw5834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5834 raw5834Labels permutation434 hz
    mixedMoment B raw5834step0 raw5834step0Labels = mixedMoment B raw5834step1 raw5834step1Labels := by
      have hz : ∀ j, raw5834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5834step1 = (fun i j => raw5834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5834step1 raw5834step0; decide +kernel
      have hl : raw5834step1Labels = raw5834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5834step0 raw5834step0Labels permutation80 hz
    mixedMoment B raw5834step1 raw5834step1Labels = mixedMoment B raw5834step2 raw5834step2Labels := by
      have ha : raw5834step2 = (fun i j => raw5834step1 (permutation20 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5834step2 raw5834step1; decide +kernel
      have hl : raw5834step2Labels = raw5834step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5834step1 raw5834step1Labels permutation20 permutation5
    mixedMoment B raw5834step2 raw5834step2Labels = mixedMoment B raw5834step3 raw5834step3Labels := by
      have ha : raw5834step3 = -raw5834step2 := by apply Matrix.ext; change ∀ i j, raw5834step3 i j = -(raw5834step2 i j); unfold raw5834step3 raw5834step2; decide +kernel
      have hl : raw5834step3Labels = raw5834step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5834step3 raw5834step3Labels = mixedMoment B raw5834step4 raw5834step4Labels := by
      have ha : raw5834step4 = raw5834step3 := by apply Matrix.ext; unfold raw5834step4 raw5834step3; decide +kernel
      have hl : raw5834step3Labels = labelEmbedding1 ∘ raw5834step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5834step3 raw5834step3Labels raw5834step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

def raw5835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5835step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5835step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw5835step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5835step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw5835step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5835 raw5835Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw5835 raw5835Labels = mixedMoment B raw5835step0 raw5835step0Labels := by
      have hz : ∀ j, raw5835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5835step0 = (fun i j => raw5835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5835step0 raw5835; decide +kernel
      have hl : raw5835step0Labels = raw5835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5835 raw5835Labels permutation434 hz
    mixedMoment B raw5835step0 raw5835step0Labels = mixedMoment B raw5835step1 raw5835step1Labels := by
      have hz : ∀ j, raw5835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5835step1 = (fun i j => raw5835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5835step1 raw5835step0; decide +kernel
      have hl : raw5835step1Labels = raw5835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5835step0 raw5835step0Labels permutation80 hz
    mixedMoment B raw5835step1 raw5835step1Labels = mixedMoment B raw5835step2 raw5835step2Labels := by
      have ha : raw5835step2 = (fun i j => raw5835step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5835step2 raw5835step1; decide +kernel
      have hl : raw5835step2Labels = raw5835step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5835step1 raw5835step1Labels permutation25 permutation7
    mixedMoment B raw5835step2 raw5835step2Labels = mixedMoment B raw5835step3 raw5835step3Labels := by
      have ha : raw5835step3 = raw5835step2 := by apply Matrix.ext; unfold raw5835step3 raw5835step2; decide +kernel
      have hl : raw5835step2Labels = labelEmbedding1 ∘ raw5835step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5835step2 raw5835step2Labels raw5835step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw5836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5836step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5836step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5836step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw5836step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5836step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw5836step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5836 raw5836Labels = mixedMoment B node3049 node3049Labels := by
  calc
    mixedMoment B raw5836 raw5836Labels = mixedMoment B raw5836step0 raw5836step0Labels := by
      have hz : ∀ j, raw5836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5836step0 = (fun i j => raw5836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5836step0 raw5836; decide +kernel
      have hl : raw5836step0Labels = raw5836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5836 raw5836Labels permutation434 hz
    mixedMoment B raw5836step0 raw5836step0Labels = mixedMoment B raw5836step1 raw5836step1Labels := by
      have hz : ∀ j, raw5836step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5836step1 = (fun i j => raw5836step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5836step1 raw5836step0; decide +kernel
      have hl : raw5836step1Labels = raw5836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5836step0 raw5836step0Labels permutation80 hz
    mixedMoment B raw5836step1 raw5836step1Labels = mixedMoment B raw5836step2 raw5836step2Labels := by
      have ha : raw5836step2 = (fun i j => raw5836step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5836step2 raw5836step1; decide +kernel
      have hl : raw5836step2Labels = raw5836step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5836step1 raw5836step1Labels permutation25 permutation7
    mixedMoment B raw5836step2 raw5836step2Labels = mixedMoment B raw5836step3 raw5836step3Labels := by
      have ha : raw5836step3 = raw5836step2 := by apply Matrix.ext; unfold raw5836step3 raw5836step2; decide +kernel
      have hl : raw5836step2Labels = labelEmbedding1 ∘ raw5836step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5836step2 raw5836step2Labels raw5836step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3049 node3049Labels := by rfl

def raw5837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5837step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5837 raw5837Labels = mixedMoment B node3035 node3035Labels := by
  calc
    mixedMoment B raw5837 raw5837Labels = mixedMoment B raw5837step0 raw5837step0Labels := by
      have hz : ∀ j, raw5837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5837step0 = (fun i j => raw5837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5837step0 raw5837; decide +kernel
      have hl : raw5837step0Labels = raw5837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5837 raw5837Labels permutation434 hz
    mixedMoment B raw5837step0 raw5837step0Labels = mixedMoment B raw5837step1 raw5837step1Labels := by
      have ha : raw5837step1 = (fun i j => raw5837step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5837step1 raw5837step0; decide +kernel
      have hl : raw5837step1Labels = raw5837step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5837step0 raw5837step0Labels permutation127 permutation7
    mixedMoment B raw5837step1 raw5837step1Labels = mixedMoment B raw5837step2 raw5837step2Labels := by
      have ha : raw5837step2 = raw5837step1 := by apply Matrix.ext; unfold raw5837step2 raw5837step1; decide +kernel
      have hl : raw5837step1Labels = labelEmbedding1 ∘ raw5837step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5837step1 raw5837step1Labels raw5837step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3035 node3035Labels := by rfl

def raw5838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5838step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5838 raw5838Labels = mixedMoment B node3035 node3035Labels := by
  calc
    mixedMoment B raw5838 raw5838Labels = mixedMoment B raw5838step0 raw5838step0Labels := by
      have hz : ∀ j, raw5838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5838step0 = (fun i j => raw5838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5838step0 raw5838; decide +kernel
      have hl : raw5838step0Labels = raw5838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5838 raw5838Labels permutation346 hz
    mixedMoment B raw5838step0 raw5838step0Labels = mixedMoment B raw5838step1 raw5838step1Labels := by
      have ha : raw5838step1 = (fun i j => raw5838step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5838step1 raw5838step0; decide +kernel
      have hl : raw5838step1Labels = raw5838step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5838step0 raw5838step0Labels permutation127 permutation7
    mixedMoment B raw5838step1 raw5838step1Labels = mixedMoment B raw5838step2 raw5838step2Labels := by
      have ha : raw5838step2 = raw5838step1 := by apply Matrix.ext; unfold raw5838step2 raw5838step1; decide +kernel
      have hl : raw5838step1Labels = labelEmbedding1 ∘ raw5838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5838step1 raw5838step1Labels raw5838step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3035 node3035Labels := by rfl

def raw5839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5839step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5839step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw5839step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5839step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw5839step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5839step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw5839step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5839 raw5839Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw5839 raw5839Labels = mixedMoment B raw5839step0 raw5839step0Labels := by
      have hz : ∀ j, raw5839 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5839step0 = (fun i j => raw5839 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5839step0 raw5839; decide +kernel
      have hl : raw5839step0Labels = raw5839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5839 raw5839Labels permutation434 hz
    mixedMoment B raw5839step0 raw5839step0Labels = mixedMoment B raw5839step1 raw5839step1Labels := by
      have hz : ∀ j, raw5839step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5839step1 = (fun i j => raw5839step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5839step1 raw5839step0; decide +kernel
      have hl : raw5839step1Labels = raw5839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5839step0 raw5839step0Labels permutation80 hz
    mixedMoment B raw5839step1 raw5839step1Labels = mixedMoment B raw5839step2 raw5839step2Labels := by
      have ha : raw5839step2 = (fun i j => raw5839step1 (permutation20 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5839step2 raw5839step1; decide +kernel
      have hl : raw5839step2Labels = raw5839step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5839step1 raw5839step1Labels permutation20 permutation5
    mixedMoment B raw5839step2 raw5839step2Labels = mixedMoment B raw5839step3 raw5839step3Labels := by
      have ha : raw5839step3 = -raw5839step2 := by apply Matrix.ext; change ∀ i j, raw5839step3 i j = -(raw5839step2 i j); unfold raw5839step3 raw5839step2; decide +kernel
      have hl : raw5839step3Labels = raw5839step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5839step3 raw5839step3Labels = mixedMoment B raw5839step4 raw5839step4Labels := by
      have ha : raw5839step4 = raw5839step3 := by apply Matrix.ext; unfold raw5839step4 raw5839step3; decide +kernel
      have hl : raw5839step3Labels = labelEmbedding1 ∘ raw5839step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5839step3 raw5839step3Labels raw5839step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3161 node3161Labels := by rfl

def raw5840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5840step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw5840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5840step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw5840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5840 raw5840Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw5840 raw5840Labels = mixedMoment B raw5840step0 raw5840step0Labels := by
      have hz : ∀ j, raw5840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5840step0 = (fun i j => raw5840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5840step0 raw5840; decide +kernel
      have hl : raw5840step0Labels = raw5840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5840 raw5840Labels permutation434 hz
    mixedMoment B raw5840step0 raw5840step0Labels = mixedMoment B raw5840step1 raw5840step1Labels := by
      have hz : ∀ j, raw5840step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5840step1 = (fun i j => raw5840step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5840step1 raw5840step0; decide +kernel
      have hl : raw5840step1Labels = raw5840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5840step0 raw5840step0Labels permutation80 hz
    mixedMoment B raw5840step1 raw5840step1Labels = mixedMoment B raw5840step2 raw5840step2Labels := by
      have ha : raw5840step2 = (fun i j => raw5840step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5840step2 raw5840step1; decide +kernel
      have hl : raw5840step2Labels = raw5840step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5840step1 raw5840step1Labels permutation25 permutation7
    mixedMoment B raw5840step2 raw5840step2Labels = mixedMoment B raw5840step3 raw5840step3Labels := by
      have ha : raw5840step3 = raw5840step2 := by apply Matrix.ext; unfold raw5840step3 raw5840step2; decide +kernel
      have hl : raw5840step2Labels = labelEmbedding1 ∘ raw5840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5840step2 raw5840step2Labels raw5840step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw5841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5841step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5841 raw5841Labels = mixedMoment B node3022 node3022Labels := by
  calc
    mixedMoment B raw5841 raw5841Labels = mixedMoment B raw5841step0 raw5841step0Labels := by
      have hz : ∀ j, raw5841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5841step0 = (fun i j => raw5841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5841step0 raw5841; decide +kernel
      have hl : raw5841step0Labels = raw5841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5841 raw5841Labels permutation434 hz
    mixedMoment B raw5841step0 raw5841step0Labels = mixedMoment B raw5841step1 raw5841step1Labels := by
      have ha : raw5841step1 = (fun i j => raw5841step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5841step1 raw5841step0; decide +kernel
      have hl : raw5841step1Labels = raw5841step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5841step0 raw5841step0Labels permutation127 permutation7
    mixedMoment B raw5841step1 raw5841step1Labels = mixedMoment B raw5841step2 raw5841step2Labels := by
      have ha : raw5841step2 = raw5841step1 := by apply Matrix.ext; unfold raw5841step2 raw5841step1; decide +kernel
      have hl : raw5841step1Labels = labelEmbedding1 ∘ raw5841step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5841step1 raw5841step1Labels raw5841step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3022 node3022Labels := by rfl

def raw5842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5842step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5842 raw5842Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw5842 raw5842Labels = mixedMoment B raw5842step0 raw5842step0Labels := by
      have hz : ∀ j, raw5842 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5842step0 = (fun i j => raw5842 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5842step0 raw5842; decide +kernel
      have hl : raw5842step0Labels = raw5842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5842 raw5842Labels permutation434 hz
    mixedMoment B raw5842step0 raw5842step0Labels = mixedMoment B raw5842step1 raw5842step1Labels := by
      have ha : raw5842step1 = (fun i j => raw5842step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5842step1 raw5842step0; decide +kernel
      have hl : raw5842step1Labels = raw5842step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5842step0 raw5842step0Labels permutation127 permutation7
    mixedMoment B raw5842step1 raw5842step1Labels = mixedMoment B raw5842step2 raw5842step2Labels := by
      have ha : raw5842step2 = raw5842step1 := by apply Matrix.ext; unfold raw5842step2 raw5842step1; decide +kernel
      have hl : raw5842step1Labels = labelEmbedding1 ∘ raw5842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5842step1 raw5842step1Labels raw5842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw5843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5843step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5843 raw5843Labels = mixedMoment B node3015 node3015Labels := by
  calc
    mixedMoment B raw5843 raw5843Labels = mixedMoment B raw5843step0 raw5843step0Labels := by
      have ha : raw5843step0 = (fun i j => raw5843 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5843step0 raw5843; decide +kernel
      have hl : raw5843step0Labels = raw5843Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5843 raw5843Labels permutation584 permutation7
    mixedMoment B raw5843step0 raw5843step0Labels = mixedMoment B raw5843step1 raw5843step1Labels := by
      have ha : raw5843step1 = raw5843step0 := by apply Matrix.ext; unfold raw5843step1 raw5843step0; decide +kernel
      have hl : raw5843step0Labels = labelEmbedding1 ∘ raw5843step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5843step0 raw5843step0Labels raw5843step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3015 node3015Labels := by rfl

def raw5844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5844step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5844step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5844step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5844step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5844 raw5844Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw5844 raw5844Labels = mixedMoment B raw5844step0 raw5844step0Labels := by
      have hz : ∀ j, raw5844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5844step0 = (fun i j => raw5844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5844step0 raw5844; decide +kernel
      have hl : raw5844step0Labels = raw5844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5844 raw5844Labels permutation434 hz
    mixedMoment B raw5844step0 raw5844step0Labels = mixedMoment B raw5844step1 raw5844step1Labels := by
      have ha : raw5844step1 = (fun i j => raw5844step0 (permutation104 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5844step1 raw5844step0; decide +kernel
      have hl : raw5844step1Labels = raw5844step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5844step0 raw5844step0Labels permutation104 permutation5
    mixedMoment B raw5844step1 raw5844step1Labels = mixedMoment B raw5844step2 raw5844step2Labels := by
      have ha : raw5844step2 = -raw5844step1 := by apply Matrix.ext; change ∀ i j, raw5844step2 i j = -(raw5844step1 i j); unfold raw5844step2 raw5844step1; decide +kernel
      have hl : raw5844step2Labels = raw5844step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5844step2 raw5844step2Labels = mixedMoment B raw5844step3 raw5844step3Labels := by
      have ha : raw5844step3 = raw5844step2 := by apply Matrix.ext; unfold raw5844step3 raw5844step2; decide +kernel
      have hl : raw5844step2Labels = labelEmbedding1 ∘ raw5844step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5844step2 raw5844step2Labels raw5844step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw5845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5845step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5845 raw5845Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw5845 raw5845Labels = mixedMoment B raw5845step0 raw5845step0Labels := by
      have hz : ∀ j, raw5845 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5845step0 = (fun i j => raw5845 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5845step0 raw5845; decide +kernel
      have hl : raw5845step0Labels = raw5845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5845 raw5845Labels permutation434 hz
    mixedMoment B raw5845step0 raw5845step0Labels = mixedMoment B raw5845step1 raw5845step1Labels := by
      have ha : raw5845step1 = (fun i j => raw5845step0 (permutation121 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5845step1 raw5845step0; decide +kernel
      have hl : raw5845step1Labels = raw5845step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5845step0 raw5845step0Labels permutation121 permutation7
    mixedMoment B raw5845step1 raw5845step1Labels = mixedMoment B raw5845step2 raw5845step2Labels := by
      have ha : raw5845step2 = raw5845step1 := by apply Matrix.ext; unfold raw5845step2 raw5845step1; decide +kernel
      have hl : raw5845step1Labels = labelEmbedding1 ∘ raw5845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5845step1 raw5845step1Labels raw5845step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw5846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5846step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5846step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5846 raw5846Labels = mixedMoment B node3022 node3022Labels := by
  calc
    mixedMoment B raw5846 raw5846Labels = mixedMoment B raw5846step0 raw5846step0Labels := by
      have hz : ∀ j, raw5846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5846step0 = (fun i j => raw5846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5846step0 raw5846; decide +kernel
      have hl : raw5846step0Labels = raw5846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5846 raw5846Labels permutation346 hz
    mixedMoment B raw5846step0 raw5846step0Labels = mixedMoment B raw5846step1 raw5846step1Labels := by
      have ha : raw5846step1 = (fun i j => raw5846step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5846step1 raw5846step0; decide +kernel
      have hl : raw5846step1Labels = raw5846step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5846step0 raw5846step0Labels permutation127 permutation7
    mixedMoment B raw5846step1 raw5846step1Labels = mixedMoment B raw5846step2 raw5846step2Labels := by
      have ha : raw5846step2 = raw5846step1 := by apply Matrix.ext; unfold raw5846step2 raw5846step1; decide +kernel
      have hl : raw5846step1Labels = labelEmbedding1 ∘ raw5846step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5846step1 raw5846step1Labels raw5846step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3022 node3022Labels := by rfl

def raw5847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5847Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5847step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5847step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5847step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5847 raw5847Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw5847 raw5847Labels = mixedMoment B raw5847step0 raw5847step0Labels := by
      have hz : ∀ j, raw5847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5847step0 = (fun i j => raw5847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5847step0 raw5847; decide +kernel
      have hl : raw5847step0Labels = raw5847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5847 raw5847Labels permutation346 hz
    mixedMoment B raw5847step0 raw5847step0Labels = mixedMoment B raw5847step1 raw5847step1Labels := by
      have ha : raw5847step1 = (fun i j => raw5847step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5847step1 raw5847step0; decide +kernel
      have hl : raw5847step1Labels = raw5847step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5847step0 raw5847step0Labels permutation127 permutation7
    mixedMoment B raw5847step1 raw5847step1Labels = mixedMoment B raw5847step2 raw5847step2Labels := by
      have ha : raw5847step2 = raw5847step1 := by apply Matrix.ext; unfold raw5847step2 raw5847step1; decide +kernel
      have hl : raw5847step1Labels = labelEmbedding1 ∘ raw5847step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5847step1 raw5847step1Labels raw5847step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw5848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5848Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5848 raw5848Labels = mixedMoment B node3015 node3015Labels := by
  calc
    mixedMoment B raw5848 raw5848Labels = mixedMoment B raw5848step0 raw5848step0Labels := by
      have ha : raw5848step0 = (fun i j => raw5848 (permutation589 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5848step0 raw5848; decide +kernel
      have hl : raw5848step0Labels = raw5848Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5848 raw5848Labels permutation589 permutation7
    mixedMoment B raw5848step0 raw5848step0Labels = mixedMoment B raw5848step1 raw5848step1Labels := by
      have ha : raw5848step1 = raw5848step0 := by apply Matrix.ext; unfold raw5848step1 raw5848step0; decide +kernel
      have hl : raw5848step0Labels = labelEmbedding1 ∘ raw5848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5848step0 raw5848step0Labels raw5848step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3015 node3015Labels := by rfl

def raw5849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5849Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5849step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5849step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5849step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5849step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5849step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5849 raw5849Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw5849 raw5849Labels = mixedMoment B raw5849step0 raw5849step0Labels := by
      have hz : ∀ j, raw5849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5849step0 = (fun i j => raw5849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5849step0 raw5849; decide +kernel
      have hl : raw5849step0Labels = raw5849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5849 raw5849Labels permutation346 hz
    mixedMoment B raw5849step0 raw5849step0Labels = mixedMoment B raw5849step1 raw5849step1Labels := by
      have ha : raw5849step1 = (fun i j => raw5849step0 (permutation104 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5849step1 raw5849step0; decide +kernel
      have hl : raw5849step1Labels = raw5849step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5849step0 raw5849step0Labels permutation104 permutation5
    mixedMoment B raw5849step1 raw5849step1Labels = mixedMoment B raw5849step2 raw5849step2Labels := by
      have ha : raw5849step2 = -raw5849step1 := by apply Matrix.ext; change ∀ i j, raw5849step2 i j = -(raw5849step1 i j); unfold raw5849step2 raw5849step1; decide +kernel
      have hl : raw5849step2Labels = raw5849step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5849step2 raw5849step2Labels = mixedMoment B raw5849step3 raw5849step3Labels := by
      have ha : raw5849step3 = raw5849step2 := by apply Matrix.ext; unfold raw5849step3 raw5849step2; decide +kernel
      have hl : raw5849step2Labels = labelEmbedding1 ∘ raw5849step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5849step2 raw5849step2Labels raw5849step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw5850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5850Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5850step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5850 raw5850Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw5850 raw5850Labels = mixedMoment B raw5850step0 raw5850step0Labels := by
      have hz : ∀ j, raw5850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5850step0 = (fun i j => raw5850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5850step0 raw5850; decide +kernel
      have hl : raw5850step0Labels = raw5850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5850 raw5850Labels permutation346 hz
    mixedMoment B raw5850step0 raw5850step0Labels = mixedMoment B raw5850step1 raw5850step1Labels := by
      have ha : raw5850step1 = (fun i j => raw5850step0 (permutation121 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5850step1 raw5850step0; decide +kernel
      have hl : raw5850step1Labels = raw5850step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5850step0 raw5850step0Labels permutation121 permutation7
    mixedMoment B raw5850step1 raw5850step1Labels = mixedMoment B raw5850step2 raw5850step2Labels := by
      have ha : raw5850step2 = raw5850step1 := by apply Matrix.ext; unfold raw5850step2 raw5850step1; decide +kernel
      have hl : raw5850step1Labels = labelEmbedding1 ∘ raw5850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5850step1 raw5850step1Labels raw5850step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw5851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5851Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5851step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5851step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw5851step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw5851step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5851 raw5851Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw5851 raw5851Labels = mixedMoment B raw5851step0 raw5851step0Labels := by
      have hz : ∀ j, raw5851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5851step0 = (fun i j => raw5851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5851step0 raw5851; decide +kernel
      have hl : raw5851step0Labels = raw5851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5851 raw5851Labels permutation434 hz
    mixedMoment B raw5851step0 raw5851step0Labels = mixedMoment B raw5851step1 raw5851step1Labels := by
      have hz : ∀ j, raw5851step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5851step1 = (fun i j => raw5851step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5851step1 raw5851step0; decide +kernel
      have hl : raw5851step1Labels = raw5851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5851step0 raw5851step0Labels permutation80 hz
    mixedMoment B raw5851step1 raw5851step1Labels = mixedMoment B raw5851step2 raw5851step2Labels := by
      have ha : raw5851step2 = (fun i j => raw5851step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5851step2 raw5851step1; decide +kernel
      have hl : raw5851step2Labels = raw5851step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5851step1 raw5851step1Labels permutation25 permutation7
    mixedMoment B raw5851step2 raw5851step2Labels = mixedMoment B raw5851step3 raw5851step3Labels := by
      have ha : raw5851step3 = raw5851step2 := by apply Matrix.ext; unfold raw5851step3 raw5851step2; decide +kernel
      have hl : raw5851step2Labels = labelEmbedding1 ∘ raw5851step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5851step2 raw5851step2Labels raw5851step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw5852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5852step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5852step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5852step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw5852step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5852step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw5852step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5852 raw5852Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw5852 raw5852Labels = mixedMoment B raw5852step0 raw5852step0Labels := by
      have hz : ∀ j, raw5852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5852step0 = (fun i j => raw5852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5852step0 raw5852; decide +kernel
      have hl : raw5852step0Labels = raw5852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5852 raw5852Labels permutation434 hz
    mixedMoment B raw5852step0 raw5852step0Labels = mixedMoment B raw5852step1 raw5852step1Labels := by
      have hz : ∀ j, raw5852step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5852step1 = (fun i j => raw5852step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5852step1 raw5852step0; decide +kernel
      have hl : raw5852step1Labels = raw5852step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5852step0 raw5852step0Labels permutation80 hz
    mixedMoment B raw5852step1 raw5852step1Labels = mixedMoment B raw5852step2 raw5852step2Labels := by
      have ha : raw5852step2 = (fun i j => raw5852step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5852step2 raw5852step1; decide +kernel
      have hl : raw5852step2Labels = raw5852step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5852step1 raw5852step1Labels permutation25 permutation7
    mixedMoment B raw5852step2 raw5852step2Labels = mixedMoment B raw5852step3 raw5852step3Labels := by
      have ha : raw5852step3 = raw5852step2 := by apply Matrix.ext; unfold raw5852step3 raw5852step2; decide +kernel
      have hl : raw5852step2Labels = labelEmbedding1 ∘ raw5852step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5852step2 raw5852step2Labels raw5852step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw5853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5853step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5853 raw5853Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw5853 raw5853Labels = mixedMoment B raw5853step0 raw5853step0Labels := by
      have hz : ∀ j, raw5853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5853step0 = (fun i j => raw5853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5853step0 raw5853; decide +kernel
      have hl : raw5853step0Labels = raw5853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5853 raw5853Labels permutation434 hz
    mixedMoment B raw5853step0 raw5853step0Labels = mixedMoment B raw5853step1 raw5853step1Labels := by
      have ha : raw5853step1 = (fun i j => raw5853step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5853step1 raw5853step0; decide +kernel
      have hl : raw5853step1Labels = raw5853step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5853step0 raw5853step0Labels permutation127 permutation7
    mixedMoment B raw5853step1 raw5853step1Labels = mixedMoment B raw5853step2 raw5853step2Labels := by
      have ha : raw5853step2 = raw5853step1 := by apply Matrix.ext; unfold raw5853step2 raw5853step1; decide +kernel
      have hl : raw5853step1Labels = labelEmbedding1 ∘ raw5853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5853step1 raw5853step1Labels raw5853step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw5854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5854 raw5854Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw5854 raw5854Labels = mixedMoment B raw5854step0 raw5854step0Labels := by
      have hz : ∀ j, raw5854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5854step0 = (fun i j => raw5854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5854step0 raw5854; decide +kernel
      have hl : raw5854step0Labels = raw5854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5854 raw5854Labels permutation346 hz
    mixedMoment B raw5854step0 raw5854step0Labels = mixedMoment B raw5854step1 raw5854step1Labels := by
      have ha : raw5854step1 = (fun i j => raw5854step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5854step1 raw5854step0; decide +kernel
      have hl : raw5854step1Labels = raw5854step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5854step0 raw5854step0Labels permutation127 permutation7
    mixedMoment B raw5854step1 raw5854step1Labels = mixedMoment B raw5854step2 raw5854step2Labels := by
      have ha : raw5854step2 = raw5854step1 := by apply Matrix.ext; unfold raw5854step2 raw5854step1; decide +kernel
      have hl : raw5854step1Labels = labelEmbedding1 ∘ raw5854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5854step1 raw5854step1Labels raw5854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw5855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw5855step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5855step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5855 raw5855Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5855 raw5855Labels = mixedMoment B raw5855step0 raw5855step0Labels := by
      have hz : ∀ j, raw5855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5855step0 = (fun i j => raw5855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5855step0 raw5855; decide +kernel
      have hl : raw5855step0Labels = raw5855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5855 raw5855Labels permutation434 hz
    mixedMoment B raw5855step0 raw5855step0Labels = mixedMoment B raw5855step1 raw5855step1Labels := by
      have hz : ∀ j, raw5855step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5855step1 = (fun i j => raw5855step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5855step1 raw5855step0; decide +kernel
      have hl : raw5855step1Labels = raw5855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5855step0 raw5855step0Labels permutation80 hz
    mixedMoment B raw5855step1 raw5855step1Labels = mixedMoment B raw5855step2 raw5855step2Labels := by
      have ha : raw5855step2 = (fun i j => raw5855step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5855step2 raw5855step1; decide +kernel
      have hl : raw5855step2Labels = raw5855step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5855step1 raw5855step1Labels permutation25 permutation7
    mixedMoment B raw5855step2 raw5855step2Labels = mixedMoment B raw5855step3 raw5855step3Labels := by
      have ha : raw5855step3 = raw5855step2 := by apply Matrix.ext; unfold raw5855step3 raw5855step2; decide +kernel
      have hl : raw5855step2Labels = labelEmbedding1 ∘ raw5855step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5855step2 raw5855step2Labels raw5855step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw5856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5856step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5856step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5856step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def raw5856step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5856step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def raw5856step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5856 raw5856Labels = mixedMoment B node2064 node2064Labels := by
  calc
    mixedMoment B raw5856 raw5856Labels = mixedMoment B raw5856step0 raw5856step0Labels := by
      have hz : ∀ j, raw5856 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5856step0 = (fun i j => raw5856 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5856step0 raw5856; decide +kernel
      have hl : raw5856step0Labels = raw5856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5856 raw5856Labels permutation434 hz
    mixedMoment B raw5856step0 raw5856step0Labels = mixedMoment B raw5856step1 raw5856step1Labels := by
      have hz : ∀ j, raw5856step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5856step1 = (fun i j => raw5856step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5856step1 raw5856step0; decide +kernel
      have hl : raw5856step1Labels = raw5856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5856step0 raw5856step0Labels permutation80 hz
    mixedMoment B raw5856step1 raw5856step1Labels = mixedMoment B raw5856step2 raw5856step2Labels := by
      have ha : raw5856step2 = (fun i j => raw5856step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5856step2 raw5856step1; decide +kernel
      have hl : raw5856step2Labels = raw5856step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5856step1 raw5856step1Labels permutation29 permutation5
    mixedMoment B raw5856step2 raw5856step2Labels = mixedMoment B raw5856step3 raw5856step3Labels := by
      have ha : raw5856step3 = raw5856step2 := by apply Matrix.ext; unfold raw5856step3 raw5856step2; decide +kernel
      have hl : raw5856step2Labels = labelEmbedding1 ∘ raw5856step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5856step2 raw5856step2Labels raw5856step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2064 node2064Labels := by rfl

def raw5857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5857step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5857step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5857step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5857step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5857step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5857 raw5857Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw5857 raw5857Labels = mixedMoment B raw5857step0 raw5857step0Labels := by
      have hz : ∀ j, raw5857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5857step0 = (fun i j => raw5857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5857step0 raw5857; decide +kernel
      have hl : raw5857step0Labels = raw5857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5857 raw5857Labels permutation434 hz
    mixedMoment B raw5857step0 raw5857step0Labels = mixedMoment B raw5857step1 raw5857step1Labels := by
      have hz : ∀ j, raw5857step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5857step1 = (fun i j => raw5857step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5857step1 raw5857step0; decide +kernel
      have hl : raw5857step1Labels = raw5857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5857step0 raw5857step0Labels permutation80 hz
    mixedMoment B raw5857step1 raw5857step1Labels = mixedMoment B raw5857step2 raw5857step2Labels := by
      have ha : raw5857step2 = (fun i j => raw5857step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5857step2 raw5857step1; decide +kernel
      have hl : raw5857step2Labels = raw5857step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5857step1 raw5857step1Labels permutation28 permutation5
    mixedMoment B raw5857step2 raw5857step2Labels = mixedMoment B raw5857step3 raw5857step3Labels := by
      have ha : raw5857step3 = raw5857step2 := by apply Matrix.ext; unfold raw5857step3 raw5857step2; decide +kernel
      have hl : raw5857step2Labels = labelEmbedding1 ∘ raw5857step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5857step2 raw5857step2Labels raw5857step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw5858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5858step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5858 raw5858Labels = mixedMoment B node2059 node2059Labels := by
  calc
    mixedMoment B raw5858 raw5858Labels = mixedMoment B raw5858step0 raw5858step0Labels := by
      have hz : ∀ j, raw5858 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5858step0 = (fun i j => raw5858 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5858step0 raw5858; decide +kernel
      have hl : raw5858step0Labels = raw5858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5858 raw5858Labels permutation434 hz
    mixedMoment B raw5858step0 raw5858step0Labels = mixedMoment B raw5858step1 raw5858step1Labels := by
      have ha : raw5858step1 = (fun i j => raw5858step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5858step1 raw5858step0; decide +kernel
      have hl : raw5858step1Labels = raw5858step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5858step0 raw5858step0Labels permutation136 permutation5
    mixedMoment B raw5858step1 raw5858step1Labels = mixedMoment B raw5858step2 raw5858step2Labels := by
      have ha : raw5858step2 = raw5858step1 := by apply Matrix.ext; unfold raw5858step2 raw5858step1; decide +kernel
      have hl : raw5858step1Labels = labelEmbedding1 ∘ raw5858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5858step1 raw5858step1Labels raw5858step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2059 node2059Labels := by rfl

def raw5859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5859 raw5859Labels = mixedMoment B node2059 node2059Labels := by
  calc
    mixedMoment B raw5859 raw5859Labels = mixedMoment B raw5859step0 raw5859step0Labels := by
      have hz : ∀ j, raw5859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5859step0 = (fun i j => raw5859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5859step0 raw5859; decide +kernel
      have hl : raw5859step0Labels = raw5859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5859 raw5859Labels permutation346 hz
    mixedMoment B raw5859step0 raw5859step0Labels = mixedMoment B raw5859step1 raw5859step1Labels := by
      have ha : raw5859step1 = (fun i j => raw5859step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5859step1 raw5859step0; decide +kernel
      have hl : raw5859step1Labels = raw5859step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5859step0 raw5859step0Labels permutation136 permutation5
    mixedMoment B raw5859step1 raw5859step1Labels = mixedMoment B raw5859step2 raw5859step2Labels := by
      have ha : raw5859step2 = raw5859step1 := by apply Matrix.ext; unfold raw5859step2 raw5859step1; decide +kernel
      have hl : raw5859step1Labels = labelEmbedding1 ∘ raw5859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5859step1 raw5859step1Labels raw5859step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2059 node2059Labels := by rfl

def raw5860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5860step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 3, -3], ![3, -3, 0]]
def raw5860step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5860step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5860step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5860 raw5860Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw5860 raw5860Labels = mixedMoment B raw5860step0 raw5860step0Labels := by
      have hz : ∀ j, raw5860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5860step0 = (fun i j => raw5860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5860step0 raw5860; decide +kernel
      have hl : raw5860step0Labels = raw5860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5860 raw5860Labels permutation434 hz
    mixedMoment B raw5860step0 raw5860step0Labels = mixedMoment B raw5860step1 raw5860step1Labels := by
      have hz : ∀ j, raw5860step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5860step1 = (fun i j => raw5860step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5860step1 raw5860step0; decide +kernel
      have hl : raw5860step1Labels = raw5860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5860step0 raw5860step0Labels permutation80 hz
    mixedMoment B raw5860step1 raw5860step1Labels = mixedMoment B raw5860step2 raw5860step2Labels := by
      have ha : raw5860step2 = (fun i j => raw5860step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5860step2 raw5860step1; decide +kernel
      have hl : raw5860step2Labels = raw5860step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5860step1 raw5860step1Labels permutation28 permutation5
    mixedMoment B raw5860step2 raw5860step2Labels = mixedMoment B raw5860step3 raw5860step3Labels := by
      have ha : raw5860step3 = raw5860step2 := by apply Matrix.ext; unfold raw5860step3 raw5860step2; decide +kernel
      have hl : raw5860step2Labels = labelEmbedding1 ∘ raw5860step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5860step2 raw5860step2Labels raw5860step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2063 node2063Labels := by rfl

def raw5861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5861 raw5861Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw5861 raw5861Labels = mixedMoment B raw5861step0 raw5861step0Labels := by
      have hz : ∀ j, raw5861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5861step0 = (fun i j => raw5861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5861step0 raw5861; decide +kernel
      have hl : raw5861step0Labels = raw5861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5861 raw5861Labels permutation434 hz
    mixedMoment B raw5861step0 raw5861step0Labels = mixedMoment B raw5861step1 raw5861step1Labels := by
      have hz : ∀ j, raw5861step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5861step1 = (fun i j => raw5861step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5861step1 raw5861step0; decide +kernel
      have hl : raw5861step1Labels = raw5861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5861step0 raw5861step0Labels permutation80 hz
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw5862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5862step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw5862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5862step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5862step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5862 raw5862Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw5862 raw5862Labels = mixedMoment B raw5862step0 raw5862step0Labels := by
      have hz : ∀ j, raw5862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5862step0 = (fun i j => raw5862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5862step0 raw5862; decide +kernel
      have hl : raw5862step0Labels = raw5862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5862 raw5862Labels permutation434 hz
    mixedMoment B raw5862step0 raw5862step0Labels = mixedMoment B raw5862step1 raw5862step1Labels := by
      have hz : ∀ j, raw5862step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5862step1 = (fun i j => raw5862step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5862step1 raw5862step0; decide +kernel
      have hl : raw5862step1Labels = raw5862step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5862step0 raw5862step0Labels permutation80 hz
    mixedMoment B raw5862step1 raw5862step1Labels = mixedMoment B raw5862step2 raw5862step2Labels := by
      have ha : raw5862step2 = (fun i j => raw5862step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5862step2 raw5862step1; decide +kernel
      have hl : raw5862step2Labels = raw5862step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5862step1 raw5862step1Labels permutation22 permutation4
    mixedMoment B raw5862step2 raw5862step2Labels = mixedMoment B raw5862step3 raw5862step3Labels := by
      have ha : raw5862step3 = -raw5862step2 := by apply Matrix.ext; change ∀ i j, raw5862step3 i j = -(raw5862step2 i j); unfold raw5862step3 raw5862step2; decide +kernel
      have hl : raw5862step3Labels = raw5862step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw5863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5863 raw5863Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw5863 raw5863Labels = mixedMoment B raw5863step0 raw5863step0Labels := by
      have hz : ∀ j, raw5863 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5863step0 = (fun i j => raw5863 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5863step0 raw5863; decide +kernel
      have hl : raw5863step0Labels = raw5863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5863 raw5863Labels permutation434 hz
    mixedMoment B raw5863step0 raw5863step0Labels = mixedMoment B raw5863step1 raw5863step1Labels := by
      have ha : raw5863step1 = (fun i j => raw5863step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5863step1 raw5863step0; decide +kernel
      have hl : raw5863step1Labels = raw5863step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5863step0 raw5863step0Labels permutation116 permutation4
    mixedMoment B raw5863step1 raw5863step1Labels = mixedMoment B raw5863step2 raw5863step2Labels := by
      have ha : raw5863step2 = -raw5863step1 := by apply Matrix.ext; change ∀ i j, raw5863step2 i j = -(raw5863step1 i j); unfold raw5863step2 raw5863step1; decide +kernel
      have hl : raw5863step2Labels = raw5863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw5864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5864 raw5864Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw5864 raw5864Labels = mixedMoment B raw5864step0 raw5864step0Labels := by
      have hz : ∀ j, raw5864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5864step0 = (fun i j => raw5864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5864step0 raw5864; decide +kernel
      have hl : raw5864step0Labels = raw5864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5864 raw5864Labels permutation346 hz
    mixedMoment B raw5864step0 raw5864step0Labels = mixedMoment B raw5864step1 raw5864step1Labels := by
      have ha : raw5864step1 = (fun i j => raw5864step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5864step1 raw5864step0; decide +kernel
      have hl : raw5864step1Labels = raw5864step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5864step0 raw5864step0Labels permutation116 permutation4
    mixedMoment B raw5864step1 raw5864step1Labels = mixedMoment B raw5864step2 raw5864step2Labels := by
      have ha : raw5864step2 = -raw5864step1 := by apply Matrix.ext; change ∀ i j, raw5864step2 i j = -(raw5864step1 i j); unfold raw5864step2 raw5864step1; decide +kernel
      have hl : raw5864step2Labels = raw5864step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw5865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5865step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5865step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5865 raw5865Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw5865 raw5865Labels = mixedMoment B raw5865step0 raw5865step0Labels := by
      have hz : ∀ j, raw5865 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5865step0 = (fun i j => raw5865 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5865step0 raw5865; decide +kernel
      have hl : raw5865step0Labels = raw5865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5865 raw5865Labels permutation434 hz
    mixedMoment B raw5865step0 raw5865step0Labels = mixedMoment B raw5865step1 raw5865step1Labels := by
      have hz : ∀ j, raw5865step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5865step1 = (fun i j => raw5865step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5865step1 raw5865step0; decide +kernel
      have hl : raw5865step1Labels = raw5865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5865step0 raw5865step0Labels permutation80 hz
    mixedMoment B raw5865step1 raw5865step1Labels = mixedMoment B raw5865step2 raw5865step2Labels := by
      have ha : raw5865step2 = (fun i j => raw5865step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5865step2 raw5865step1; decide +kernel
      have hl : raw5865step2Labels = raw5865step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5865step1 raw5865step1Labels permutation20 permutation4
    mixedMoment B raw5865step2 raw5865step2Labels = mixedMoment B raw5865step3 raw5865step3Labels := by
      have ha : raw5865step3 = -raw5865step2 := by apply Matrix.ext; change ∀ i j, raw5865step3 i j = -(raw5865step2 i j); unfold raw5865step3 raw5865step2; decide +kernel
      have hl : raw5865step3Labels = raw5865step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw5866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw5866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5866step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw5866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5866 raw5866Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw5866 raw5866Labels = mixedMoment B raw5866step0 raw5866step0Labels := by
      have hz : ∀ j, raw5866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5866step0 = (fun i j => raw5866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5866step0 raw5866; decide +kernel
      have hl : raw5866step0Labels = raw5866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5866 raw5866Labels permutation434 hz
    mixedMoment B raw5866step0 raw5866step0Labels = mixedMoment B raw5866step1 raw5866step1Labels := by
      have hz : ∀ j, raw5866step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5866step1 = (fun i j => raw5866step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5866step1 raw5866step0; decide +kernel
      have hl : raw5866step1Labels = raw5866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5866step0 raw5866step0Labels permutation80 hz
    mixedMoment B raw5866step1 raw5866step1Labels = mixedMoment B raw5866step2 raw5866step2Labels := by
      have ha : raw5866step2 = (fun i j => raw5866step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5866step2 raw5866step1; decide +kernel
      have hl : raw5866step2Labels = raw5866step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5866step1 raw5866step1Labels permutation21 permutation4
    mixedMoment B raw5866step2 raw5866step2Labels = mixedMoment B raw5866step3 raw5866step3Labels := by
      have ha : raw5866step3 = -raw5866step2 := by apply Matrix.ext; change ∀ i j, raw5866step3 i j = -(raw5866step2 i j); unfold raw5866step3 raw5866step2; decide +kernel
      have hl : raw5866step3Labels = raw5866step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

def raw5867 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3], ![0, 0]]
def raw5867Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5867step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw5867step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5867step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]
def raw5867step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5867step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw5867step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5867step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw5867step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5867step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5867step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5867 raw5867Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5867 raw5867Labels = mixedMoment B raw5867step0 raw5867step0Labels := by
      have hz : ∀ j, raw5867 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw5867step0 = (fun i j => raw5867 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw5867step0 raw5867; decide +kernel
      have hl : raw5867step0Labels = raw5867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5867 raw5867Labels permutation590 hz
    mixedMoment B raw5867step0 raw5867step0Labels = mixedMoment B raw5867step1 raw5867step1Labels := by
      have hz : ∀ j, raw5867step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5867step1 = (fun i j => raw5867step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5867step1 raw5867step0; decide +kernel
      have hl : raw5867step1Labels = raw5867step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5867step0 raw5867step0Labels permutation104 hz
    mixedMoment B raw5867step1 raw5867step1Labels = mixedMoment B raw5867step2 raw5867step2Labels := by
      have hz : ∀ j, raw5867step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5867step2 = (fun i j => raw5867step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5867step2 raw5867step1; decide +kernel
      have hl : raw5867step2Labels = raw5867step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5867step1 raw5867step1Labels permutation20 hz
    mixedMoment B raw5867step2 raw5867step2Labels = mixedMoment B raw5867step3 raw5867step3Labels := by
      have ha : raw5867step3 = (fun i j => raw5867step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5867step3 raw5867step2; decide +kernel
      have hl : raw5867step3Labels = raw5867step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5867step2 raw5867step2Labels permutation7 permutation0
    mixedMoment B raw5867step3 raw5867step3Labels = mixedMoment B raw5867step4 raw5867step4Labels := by
      have ha : raw5867step4 = -raw5867step3 := by apply Matrix.ext; change ∀ i j, raw5867step4 i j = -(raw5867step3 i j); unfold raw5867step4 raw5867step3; decide +kernel
      have hl : raw5867step4Labels = raw5867step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw5868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5868 raw5868Labels = mixedMoment B node1296 node1296Labels := by
  calc
    mixedMoment B raw5868 raw5868Labels = mixedMoment B raw5868step0 raw5868step0Labels := by
      have hz : ∀ j, raw5868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5868step0 = (fun i j => raw5868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5868step0 raw5868; decide +kernel
      have hl : raw5868step0Labels = raw5868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5868 raw5868Labels permutation434 hz
    mixedMoment B raw5868step0 raw5868step0Labels = mixedMoment B raw5868step1 raw5868step1Labels := by
      have hz : ∀ j, raw5868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5868step1 = (fun i j => raw5868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5868step1 raw5868step0; decide +kernel
      have hl : raw5868step1Labels = raw5868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5868step0 raw5868step0Labels permutation80 hz
    _ = mixedMoment B node1296 node1296Labels := by rfl

def raw5869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5869 raw5869Labels = mixedMoment B node1238 node1238Labels := by
  calc
    mixedMoment B raw5869 raw5869Labels = mixedMoment B raw5869step0 raw5869step0Labels := by
      have hz : ∀ j, raw5869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5869step0 = (fun i j => raw5869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5869step0 raw5869; decide +kernel
      have hl : raw5869step0Labels = raw5869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5869 raw5869Labels permutation434 hz
    _ = mixedMoment B node1238 node1238Labels := by rfl

def raw5870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5870 raw5870Labels = mixedMoment B node1238 node1238Labels := by
  calc
    mixedMoment B raw5870 raw5870Labels = mixedMoment B raw5870step0 raw5870step0Labels := by
      have hz : ∀ j, raw5870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5870step0 = (fun i j => raw5870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5870step0 raw5870; decide +kernel
      have hl : raw5870step0Labels = raw5870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5870 raw5870Labels permutation346 hz
    _ = mixedMoment B node1238 node1238Labels := by rfl

def raw5871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5871 raw5871Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw5871 raw5871Labels = mixedMoment B raw5871step0 raw5871step0Labels := by
      have hz : ∀ j, raw5871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5871step0 = (fun i j => raw5871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5871step0 raw5871; decide +kernel
      have hl : raw5871step0Labels = raw5871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5871 raw5871Labels permutation434 hz
    mixedMoment B raw5871step0 raw5871step0Labels = mixedMoment B raw5871step1 raw5871step1Labels := by
      have hz : ∀ j, raw5871step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5871step1 = (fun i j => raw5871step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5871step1 raw5871step0; decide +kernel
      have hl : raw5871step1Labels = raw5871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5871step0 raw5871step0Labels permutation80 hz
    mixedMoment B raw5871step1 raw5871step1Labels = mixedMoment B raw5871step2 raw5871step2Labels := by
      have ha : raw5871step2 = (fun i j => raw5871step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5871step2 raw5871step1; decide +kernel
      have hl : raw5871step2Labels = raw5871step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5871step1 raw5871step1Labels permutation9 permutation2
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw5872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5872 raw5872Labels = mixedMoment B node1244 node1244Labels := by
  calc
    mixedMoment B raw5872 raw5872Labels = mixedMoment B raw5872step0 raw5872step0Labels := by
      have hz : ∀ j, raw5872 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5872step0 = (fun i j => raw5872 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5872step0 raw5872; decide +kernel
      have hl : raw5872step0Labels = raw5872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5872 raw5872Labels permutation434 hz
    mixedMoment B raw5872step0 raw5872step0Labels = mixedMoment B raw5872step1 raw5872step1Labels := by
      have hz : ∀ j, raw5872step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5872step1 = (fun i j => raw5872step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5872step1 raw5872step0; decide +kernel
      have hl : raw5872step1Labels = raw5872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5872step0 raw5872step0Labels permutation80 hz
    _ = mixedMoment B node1244 node1244Labels := by rfl

def raw5873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5873 raw5873Labels = mixedMoment B node2592 node2592Labels := by
  calc
    mixedMoment B raw5873 raw5873Labels = mixedMoment B raw5873step0 raw5873step0Labels := by
      have hz : ∀ j, raw5873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5873step0 = (fun i j => raw5873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5873step0 raw5873; decide +kernel
      have hl : raw5873step0Labels = raw5873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5873 raw5873Labels permutation434 hz
    mixedMoment B raw5873step0 raw5873step0Labels = mixedMoment B raw5873step1 raw5873step1Labels := by
      have ha : raw5873step1 = (fun i j => raw5873step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5873step1 raw5873step0; decide +kernel
      have hl : raw5873step1Labels = raw5873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5873step0 raw5873step0Labels permutation38 permutation2
    _ = mixedMoment B node2592 node2592Labels := by rfl

def raw5874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5874 raw5874Labels = mixedMoment B node2592 node2592Labels := by
  calc
    mixedMoment B raw5874 raw5874Labels = mixedMoment B raw5874step0 raw5874step0Labels := by
      have hz : ∀ j, raw5874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5874step0 = (fun i j => raw5874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5874step0 raw5874; decide +kernel
      have hl : raw5874step0Labels = raw5874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5874 raw5874Labels permutation346 hz
    mixedMoment B raw5874step0 raw5874step0Labels = mixedMoment B raw5874step1 raw5874step1Labels := by
      have ha : raw5874step1 = (fun i j => raw5874step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5874step1 raw5874step0; decide +kernel
      have hl : raw5874step1Labels = raw5874step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5874step0 raw5874step0Labels permutation38 permutation2
    _ = mixedMoment B node2592 node2592Labels := by rfl

def raw5875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw5875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5875step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5875step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5875 raw5875Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw5875 raw5875Labels = mixedMoment B raw5875step0 raw5875step0Labels := by
      have hz : ∀ j, raw5875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5875step0 = (fun i j => raw5875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5875step0 raw5875; decide +kernel
      have hl : raw5875step0Labels = raw5875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5875 raw5875Labels permutation434 hz
    mixedMoment B raw5875step0 raw5875step0Labels = mixedMoment B raw5875step1 raw5875step1Labels := by
      have hz : ∀ j, raw5875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5875step1 = (fun i j => raw5875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5875step1 raw5875step0; decide +kernel
      have hl : raw5875step1Labels = raw5875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5875step0 raw5875step0Labels permutation80 hz
    mixedMoment B raw5875step1 raw5875step1Labels = mixedMoment B raw5875step2 raw5875step2Labels := by
      have ha : raw5875step2 = (fun i j => raw5875step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5875step2 raw5875step1; decide +kernel
      have hl : raw5875step2Labels = raw5875step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5875step1 raw5875step1Labels permutation21 permutation4
    mixedMoment B raw5875step2 raw5875step2Labels = mixedMoment B raw5875step3 raw5875step3Labels := by
      have ha : raw5875step3 = -raw5875step2 := by apply Matrix.ext; change ∀ i j, raw5875step3 i j = -(raw5875step2 i j); unfold raw5875step3 raw5875step2; decide +kernel
      have hl : raw5875step3Labels = raw5875step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2138 node2138Labels := by rfl

def raw5876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5876step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw5876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5876 raw5876Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw5876 raw5876Labels = mixedMoment B raw5876step0 raw5876step0Labels := by
      have hz : ∀ j, raw5876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5876step0 = (fun i j => raw5876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5876step0 raw5876; decide +kernel
      have hl : raw5876step0Labels = raw5876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5876 raw5876Labels permutation434 hz
    mixedMoment B raw5876step0 raw5876step0Labels = mixedMoment B raw5876step1 raw5876step1Labels := by
      have hz : ∀ j, raw5876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5876step1 = (fun i j => raw5876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5876step1 raw5876step0; decide +kernel
      have hl : raw5876step1Labels = raw5876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5876step0 raw5876step0Labels permutation80 hz
    mixedMoment B raw5876step1 raw5876step1Labels = mixedMoment B raw5876step2 raw5876step2Labels := by
      have ha : raw5876step2 = (fun i j => raw5876step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5876step2 raw5876step1; decide +kernel
      have hl : raw5876step2Labels = raw5876step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5876step1 raw5876step1Labels permutation9 permutation2
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw5877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5877 raw5877Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5877 raw5877Labels = mixedMoment B raw5877step0 raw5877step0Labels := by
      have hz : ∀ j, raw5877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5877step0 = (fun i j => raw5877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5877step0 raw5877; decide +kernel
      have hl : raw5877step0Labels = raw5877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5877 raw5877Labels permutation434 hz
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw5878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5878 raw5878Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5878 raw5878Labels = mixedMoment B raw5878step0 raw5878step0Labels := by
      have hz : ∀ j, raw5878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5878step0 = (fun i j => raw5878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5878step0 raw5878; decide +kernel
      have hl : raw5878step0Labels = raw5878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5878 raw5878Labels permutation346 hz
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw5879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5879 raw5879Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw5879 raw5879Labels = mixedMoment B raw5879step0 raw5879step0Labels := by
      have hz : ∀ j, raw5879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5879step0 = (fun i j => raw5879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5879step0 raw5879; decide +kernel
      have hl : raw5879step0Labels = raw5879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5879 raw5879Labels permutation434 hz
    mixedMoment B raw5879step0 raw5879step0Labels = mixedMoment B raw5879step1 raw5879step1Labels := by
      have hz : ∀ j, raw5879step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5879step1 = (fun i j => raw5879step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5879step1 raw5879step0; decide +kernel
      have hl : raw5879step1Labels = raw5879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5879step0 raw5879step0Labels permutation80 hz
    mixedMoment B raw5879step1 raw5879step1Labels = mixedMoment B raw5879step2 raw5879step2Labels := by
      have ha : raw5879step2 = (fun i j => raw5879step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5879step2 raw5879step1; decide +kernel
      have hl : raw5879step2Labels = raw5879step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5879step1 raw5879step1Labels permutation9 permutation2
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw5880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5880 raw5880Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw5880 raw5880Labels = mixedMoment B raw5880step0 raw5880step0Labels := by
      have hz : ∀ j, raw5880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5880step0 = (fun i j => raw5880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5880step0 raw5880; decide +kernel
      have hl : raw5880step0Labels = raw5880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5880 raw5880Labels permutation434 hz
    mixedMoment B raw5880step0 raw5880step0Labels = mixedMoment B raw5880step1 raw5880step1Labels := by
      have hz : ∀ j, raw5880step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5880step1 = (fun i j => raw5880step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5880step1 raw5880step0; decide +kernel
      have hl : raw5880step1Labels = raw5880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5880step0 raw5880step0Labels permutation80 hz
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw5881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5881 raw5881Labels = mixedMoment B node2555 node2555Labels := by
  calc
    mixedMoment B raw5881 raw5881Labels = mixedMoment B raw5881step0 raw5881step0Labels := by
      have ha : raw5881step0 = (fun i j => raw5881 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5881step0 raw5881; decide +kernel
      have hl : raw5881step0Labels = raw5881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5881 raw5881Labels permutation200 permutation2
    _ = mixedMoment B node2555 node2555Labels := by rfl

def raw5882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw5882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5882 raw5882Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw5882 raw5882Labels = mixedMoment B raw5882step0 raw5882step0Labels := by
      have hz : ∀ j, raw5882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5882step0 = (fun i j => raw5882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5882step0 raw5882; decide +kernel
      have hl : raw5882step0Labels = raw5882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5882 raw5882Labels permutation434 hz
    mixedMoment B raw5882step0 raw5882step0Labels = mixedMoment B raw5882step1 raw5882step1Labels := by
      have ha : raw5882step1 = (fun i j => raw5882step0 (permutation106 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5882step1 raw5882step0; decide +kernel
      have hl : raw5882step1Labels = raw5882step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5882step0 raw5882step0Labels permutation106 permutation4
    mixedMoment B raw5882step1 raw5882step1Labels = mixedMoment B raw5882step2 raw5882step2Labels := by
      have ha : raw5882step2 = -raw5882step1 := by apply Matrix.ext; change ∀ i j, raw5882step2 i j = -(raw5882step1 i j); unfold raw5882step2 raw5882step1; decide +kernel
      have hl : raw5882step2Labels = raw5882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2133 node2133Labels := by rfl

def raw5883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5883 raw5883Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw5883 raw5883Labels = mixedMoment B raw5883step0 raw5883step0Labels := by
      have hz : ∀ j, raw5883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5883step0 = (fun i j => raw5883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5883step0 raw5883; decide +kernel
      have hl : raw5883step0Labels = raw5883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5883 raw5883Labels permutation434 hz
    mixedMoment B raw5883step0 raw5883step0Labels = mixedMoment B raw5883step1 raw5883step1Labels := by
      have ha : raw5883step1 = (fun i j => raw5883step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5883step1 raw5883step0; decide +kernel
      have hl : raw5883step1Labels = raw5883step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5883step0 raw5883step0Labels permutation33 permutation2
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw5884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5884 raw5884Labels = mixedMoment B node2555 node2555Labels := by
  calc
    mixedMoment B raw5884 raw5884Labels = mixedMoment B raw5884step0 raw5884step0Labels := by
      have ha : raw5884step0 = (fun i j => raw5884 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5884step0 raw5884; decide +kernel
      have hl : raw5884step0Labels = raw5884Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5884 raw5884Labels permutation176 permutation2
    _ = mixedMoment B node2555 node2555Labels := by rfl

def raw5885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5885 raw5885Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw5885 raw5885Labels = mixedMoment B raw5885step0 raw5885step0Labels := by
      have hz : ∀ j, raw5885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5885step0 = (fun i j => raw5885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5885step0 raw5885; decide +kernel
      have hl : raw5885step0Labels = raw5885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5885 raw5885Labels permutation434 hz
    mixedMoment B raw5885step0 raw5885step0Labels = mixedMoment B raw5885step1 raw5885step1Labels := by
      have ha : raw5885step1 = (fun i j => raw5885step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5885step1 raw5885step0; decide +kernel
      have hl : raw5885step1Labels = raw5885step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5885step0 raw5885step0Labels permutation39 permutation2
    _ = mixedMoment B node2560 node2560Labels := by rfl

def raw5886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5886 raw5886Labels = mixedMoment B node2559 node2559Labels := by
  calc
    mixedMoment B raw5886 raw5886Labels = mixedMoment B raw5886step0 raw5886step0Labels := by
      have hz : ∀ j, raw5886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5886step0 = (fun i j => raw5886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5886step0 raw5886; decide +kernel
      have hl : raw5886step0Labels = raw5886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5886 raw5886Labels permutation434 hz
    mixedMoment B raw5886step0 raw5886step0Labels = mixedMoment B raw5886step1 raw5886step1Labels := by
      have ha : raw5886step1 = (fun i j => raw5886step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5886step1 raw5886step0; decide +kernel
      have hl : raw5886step1Labels = raw5886step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5886step0 raw5886step0Labels permutation38 permutation2
    _ = mixedMoment B node2559 node2559Labels := by rfl

def raw5887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5887 raw5887Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw5887 raw5887Labels = mixedMoment B raw5887step0 raw5887step0Labels := by
      have hz : ∀ j, raw5887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5887step0 = (fun i j => raw5887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5887step0 raw5887; decide +kernel
      have hl : raw5887step0Labels = raw5887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5887 raw5887Labels permutation346 hz
    mixedMoment B raw5887step0 raw5887step0Labels = mixedMoment B raw5887step1 raw5887step1Labels := by
      have ha : raw5887step1 = (fun i j => raw5887step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5887step1 raw5887step0; decide +kernel
      have hl : raw5887step1Labels = raw5887step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5887step0 raw5887step0Labels permutation39 permutation2
    _ = mixedMoment B node2560 node2560Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
