import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37760 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37760 raw37760Labels = mixedMoment B node1895 node1895Labels := by
  calc
    mixedMoment B raw37760 raw37760Labels = mixedMoment B raw37760step0 raw37760step0Labels := by
      have hz : ∀ j, raw37760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37760step0 = (fun i j => raw37760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37760step0 raw37760; decide +kernel
      have hl : raw37760step0Labels = raw37760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37760 raw37760Labels permutation346 hz
    mixedMoment B raw37760step0 raw37760step0Labels = mixedMoment B raw37760step1 raw37760step1Labels := by
      have ha : raw37760step1 = (fun i j => raw37760step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37760step1 raw37760step0; decide +kernel
      have hl : raw37760step1Labels = raw37760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37760step0 raw37760step0Labels permutation145 permutation2
    _ = mixedMoment B node1895 node1895Labels := by rfl

def raw37761 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![-1, 0, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw37761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37761 raw37761Labels = mixedMoment B node1893 node1893Labels := by
  calc
    mixedMoment B raw37761 raw37761Labels = mixedMoment B raw37761step0 raw37761step0Labels := by
      have hz : ∀ j, raw37761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37761step0 = (fun i j => raw37761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37761step0 raw37761; decide +kernel
      have hl : raw37761step0Labels = raw37761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37761 raw37761Labels permutation346 hz
    mixedMoment B raw37761step0 raw37761step0Labels = mixedMoment B raw37761step1 raw37761step1Labels := by
      have ha : raw37761step1 = (fun i j => raw37761step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37761step1 raw37761step0; decide +kernel
      have hl : raw37761step1Labels = raw37761step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37761step0 raw37761step0Labels permutation144 permutation2
    _ = mixedMoment B node1893 node1893Labels := by rfl

def raw37762 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37762 raw37762Labels = mixedMoment B node1889 node1889Labels := by
  calc
    mixedMoment B raw37762 raw37762Labels = mixedMoment B raw37762step0 raw37762step0Labels := by
      have ha : raw37762step0 = (fun i j => raw37762 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37762step0 raw37762; decide +kernel
      have hl : raw37762step0Labels = raw37762Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37762 raw37762Labels permutation663 permutation2
    _ = mixedMoment B node1889 node1889Labels := by rfl

def raw37763 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37763 raw37763Labels = mixedMoment B node1939 node1939Labels := by
  calc
    mixedMoment B raw37763 raw37763Labels = mixedMoment B raw37763step0 raw37763step0Labels := by
      have hz : ∀ j, raw37763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37763step0 = (fun i j => raw37763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37763step0 raw37763; decide +kernel
      have hl : raw37763step0Labels = raw37763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37763 raw37763Labels permutation346 hz
    mixedMoment B raw37763step0 raw37763step0Labels = mixedMoment B raw37763step1 raw37763step1Labels := by
      have ha : raw37763step1 = (fun i j => raw37763step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37763step1 raw37763step0; decide +kernel
      have hl : raw37763step1Labels = raw37763step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37763step0 raw37763step0Labels permutation144 permutation2
    _ = mixedMoment B node1939 node1939Labels := by rfl

def raw37764 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37764 raw37764Labels = mixedMoment B node1985 node1985Labels := by
  calc
    mixedMoment B raw37764 raw37764Labels = mixedMoment B raw37764step0 raw37764step0Labels := by
      have ha : raw37764step0 = (fun i j => raw37764 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37764step0 raw37764; decide +kernel
      have hl : raw37764step0Labels = raw37764Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37764 raw37764Labels permutation640 permutation2
    _ = mixedMoment B node1985 node1985Labels := by rfl

def raw37765 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw37765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw37765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37765 raw37765Labels = mixedMoment B node1895 node1895Labels := by
  calc
    mixedMoment B raw37765 raw37765Labels = mixedMoment B raw37765step0 raw37765step0Labels := by
      have hz : ∀ j, raw37765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37765step0 = (fun i j => raw37765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37765step0 raw37765; decide +kernel
      have hl : raw37765step0Labels = raw37765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37765 raw37765Labels permutation346 hz
    mixedMoment B raw37765step0 raw37765step0Labels = mixedMoment B raw37765step1 raw37765step1Labels := by
      have ha : raw37765step1 = (fun i j => raw37765step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37765step1 raw37765step0; decide +kernel
      have hl : raw37765step1Labels = raw37765step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37765step0 raw37765step0Labels permutation151 permutation2
    _ = mixedMoment B node1895 node1895Labels := by rfl

def raw37766 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-4, 1, 3]]
def raw37766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-4, 1, 3]]
def raw37766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37766 raw37766Labels = mixedMoment B node970 node970Labels := by
  calc
    mixedMoment B raw37766 raw37766Labels = mixedMoment B raw37766step0 raw37766step0Labels := by
      have hz : ∀ j, raw37766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37766step0 = (fun i j => raw37766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37766step0 raw37766; decide +kernel
      have hl : raw37766step0Labels = raw37766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37766 raw37766Labels permutation346 hz
    mixedMoment B raw37766step0 raw37766step0Labels = mixedMoment B raw37766step1 raw37766step1Labels := by
      have ha : raw37766step1 = (fun i j => raw37766step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37766step1 raw37766step0; decide +kernel
      have hl : raw37766step1Labels = raw37766step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37766step0 raw37766step0Labels permutation145 permutation2
    _ = mixedMoment B node970 node970Labels := by rfl

def raw37767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37767step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37767 raw37767Labels = mixedMoment B node1852 node1852Labels := by
  calc
    mixedMoment B raw37767 raw37767Labels = mixedMoment B raw37767step0 raw37767step0Labels := by
      have hz : ∀ j, raw37767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37767step0 = (fun i j => raw37767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37767step0 raw37767; decide +kernel
      have hl : raw37767step0Labels = raw37767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37767 raw37767Labels permutation346 hz
    mixedMoment B raw37767step0 raw37767step0Labels = mixedMoment B raw37767step1 raw37767step1Labels := by
      have ha : raw37767step1 = (fun i j => raw37767step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37767step1 raw37767step0; decide +kernel
      have hl : raw37767step1Labels = raw37767step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37767step0 raw37767step0Labels permutation32 permutation4
    mixedMoment B raw37767step1 raw37767step1Labels = mixedMoment B raw37767step2 raw37767step2Labels := by
      have ha : raw37767step2 = -raw37767step1 := by apply Matrix.ext; change ∀ i j, raw37767step2 i j = -(raw37767step1 i j); unfold raw37767step2 raw37767step1; decide +kernel
      have hl : raw37767step2Labels = raw37767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1852 node1852Labels := by rfl

def raw37768 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37768 raw37768Labels = mixedMoment B node3327 node3327Labels := by
  calc
    mixedMoment B raw37768 raw37768Labels = mixedMoment B raw37768step0 raw37768step0Labels := by
      have hz : ∀ j, raw37768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37768step0 = (fun i j => raw37768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37768step0 raw37768; decide +kernel
      have hl : raw37768step0Labels = raw37768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37768 raw37768Labels permutation346 hz
    mixedMoment B raw37768step0 raw37768step0Labels = mixedMoment B raw37768step1 raw37768step1Labels := by
      have ha : raw37768step1 = (fun i j => raw37768step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37768step1 raw37768step0; decide +kernel
      have hl : raw37768step1Labels = raw37768step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37768step0 raw37768step0Labels permutation32 permutation4
    mixedMoment B raw37768step1 raw37768step1Labels = mixedMoment B raw37768step2 raw37768step2Labels := by
      have ha : raw37768step2 = -raw37768step1 := by apply Matrix.ext; change ∀ i j, raw37768step2 i j = -(raw37768step1 i j); unfold raw37768step2 raw37768step1; decide +kernel
      have hl : raw37768step2Labels = raw37768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3327 node3327Labels := by rfl

def raw37769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37769 raw37769Labels = mixedMoment B node3399 node3399Labels := by
  calc
    mixedMoment B raw37769 raw37769Labels = mixedMoment B raw37769step0 raw37769step0Labels := by
      have ha : raw37769step0 = (fun i j => raw37769 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37769step0 raw37769; decide +kernel
      have hl : raw37769step0Labels = raw37769Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37769 raw37769Labels permutation152 permutation4
    mixedMoment B raw37769step0 raw37769step0Labels = mixedMoment B raw37769step1 raw37769step1Labels := by
      have ha : raw37769step1 = -raw37769step0 := by apply Matrix.ext; change ∀ i j, raw37769step1 i j = -(raw37769step0 i j); unfold raw37769step1 raw37769step0; decide +kernel
      have hl : raw37769step1Labels = raw37769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3399 node3399Labels := by rfl

def raw37770 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw37770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw37770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37770 raw37770Labels = mixedMoment B node1839 node1839Labels := by
  calc
    mixedMoment B raw37770 raw37770Labels = mixedMoment B raw37770step0 raw37770step0Labels := by
      have hz : ∀ j, raw37770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37770step0 = (fun i j => raw37770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37770step0 raw37770; decide +kernel
      have hl : raw37770step0Labels = raw37770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37770 raw37770Labels permutation346 hz
    mixedMoment B raw37770step0 raw37770step0Labels = mixedMoment B raw37770step1 raw37770step1Labels := by
      have ha : raw37770step1 = (fun i j => raw37770step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37770step1 raw37770step0; decide +kernel
      have hl : raw37770step1Labels = raw37770step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37770step0 raw37770step0Labels permutation34 permutation4
    mixedMoment B raw37770step1 raw37770step1Labels = mixedMoment B raw37770step2 raw37770step2Labels := by
      have ha : raw37770step2 = -raw37770step1 := by apply Matrix.ext; change ∀ i j, raw37770step2 i j = -(raw37770step1 i j); unfold raw37770step2 raw37770step1; decide +kernel
      have hl : raw37770step2Labels = raw37770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1839 node1839Labels := by rfl

def raw37771 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37771step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37771 raw37771Labels = mixedMoment B node1895 node1895Labels := by
  calc
    mixedMoment B raw37771 raw37771Labels = mixedMoment B raw37771step0 raw37771step0Labels := by
      have hz : ∀ j, raw37771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37771step0 = (fun i j => raw37771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37771step0 raw37771; decide +kernel
      have hl : raw37771step0Labels = raw37771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37771 raw37771Labels permutation346 hz
    mixedMoment B raw37771step0 raw37771step0Labels = mixedMoment B raw37771step1 raw37771step1Labels := by
      have ha : raw37771step1 = (fun i j => raw37771step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37771step1 raw37771step0; decide +kernel
      have hl : raw37771step1Labels = raw37771step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37771step0 raw37771step0Labels permutation145 permutation4
    _ = mixedMoment B node1895 node1895Labels := by rfl

def raw37772 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37772 raw37772Labels = mixedMoment B node1888 node1888Labels := by
  calc
    mixedMoment B raw37772 raw37772Labels = mixedMoment B raw37772step0 raw37772step0Labels := by
      have ha : raw37772step0 = (fun i j => raw37772 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37772step0 raw37772; decide +kernel
      have hl : raw37772step0Labels = raw37772Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37772 raw37772Labels permutation664 permutation4
    _ = mixedMoment B node1888 node1888Labels := by rfl

def raw37773 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -3, 3]]
def raw37773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![0, -3, 3]]
def raw37773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37773 raw37773Labels = mixedMoment B node1938 node1938Labels := by
  calc
    mixedMoment B raw37773 raw37773Labels = mixedMoment B raw37773step0 raw37773step0Labels := by
      have hz : ∀ j, raw37773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37773step0 = (fun i j => raw37773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37773step0 raw37773; decide +kernel
      have hl : raw37773step0Labels = raw37773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37773 raw37773Labels permutation346 hz
    mixedMoment B raw37773step0 raw37773step0Labels = mixedMoment B raw37773step1 raw37773step1Labels := by
      have ha : raw37773step1 = (fun i j => raw37773step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37773step1 raw37773step0; decide +kernel
      have hl : raw37773step1Labels = raw37773step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37773step0 raw37773step0Labels permutation145 permutation4
    _ = mixedMoment B node1938 node1938Labels := by rfl

def raw37774 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw37774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37774 raw37774Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw37774 raw37774Labels = mixedMoment B raw37774step0 raw37774step0Labels := by
      have hz : ∀ j, raw37774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37774step0 = (fun i j => raw37774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37774step0 raw37774; decide +kernel
      have hl : raw37774step0Labels = raw37774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37774 raw37774Labels permutation346 hz
    mixedMoment B raw37774step0 raw37774step0Labels = mixedMoment B raw37774step1 raw37774step1Labels := by
      have ha : raw37774step1 = (fun i j => raw37774step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37774step1 raw37774step0; decide +kernel
      have hl : raw37774step1Labels = raw37774step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37774step0 raw37774step0Labels permutation32 permutation4
    mixedMoment B raw37774step1 raw37774step1Labels = mixedMoment B raw37774step2 raw37774step2Labels := by
      have ha : raw37774step2 = -raw37774step1 := by apply Matrix.ext; change ∀ i j, raw37774step2 i j = -(raw37774step1 i j); unfold raw37774step2 raw37774step1; decide +kernel
      have hl : raw37774step2Labels = raw37774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3591 node3591Labels := by rfl

def raw37775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw37775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw37775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37775 raw37775Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw37775 raw37775Labels = mixedMoment B raw37775step0 raw37775step0Labels := by
      have hz : ∀ j, raw37775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37775step0 = (fun i j => raw37775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37775step0 raw37775; decide +kernel
      have hl : raw37775step0Labels = raw37775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37775 raw37775Labels permutation346 hz
    mixedMoment B raw37775step0 raw37775step0Labels = mixedMoment B raw37775step1 raw37775step1Labels := by
      have ha : raw37775step1 = (fun i j => raw37775step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37775step1 raw37775step0; decide +kernel
      have hl : raw37775step1Labels = raw37775step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37775step0 raw37775step0Labels permutation40 permutation4
    mixedMoment B raw37775step1 raw37775step1Labels = mixedMoment B raw37775step2 raw37775step2Labels := by
      have ha : raw37775step2 = -raw37775step1 := by apply Matrix.ext; change ∀ i j, raw37775step2 i j = -(raw37775step1 i j); unfold raw37775step2 raw37775step1; decide +kernel
      have hl : raw37775step2Labels = raw37775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2249 node2249Labels := by rfl

def raw37776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw37776step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37776 raw37776Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw37776 raw37776Labels = mixedMoment B raw37776step0 raw37776step0Labels := by
      have ha : raw37776step0 = (fun i j => raw37776 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37776step0 raw37776; decide +kernel
      have hl : raw37776step0Labels = raw37776Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37776 raw37776Labels permutation160 permutation4
    mixedMoment B raw37776step0 raw37776step0Labels = mixedMoment B raw37776step1 raw37776step1Labels := by
      have ha : raw37776step1 = -raw37776step0 := by apply Matrix.ext; change ∀ i j, raw37776step1 i j = -(raw37776step0 i j); unfold raw37776step1 raw37776step0; decide +kernel
      have hl : raw37776step1Labels = raw37776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2144 node2144Labels := by rfl

def raw37777 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37777 raw37777Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw37777 raw37777Labels = mixedMoment B raw37777step0 raw37777step0Labels := by
      have hz : ∀ j, raw37777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37777step0 = (fun i j => raw37777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37777step0 raw37777; decide +kernel
      have hl : raw37777step0Labels = raw37777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37777 raw37777Labels permutation346 hz
    mixedMoment B raw37777step0 raw37777step0Labels = mixedMoment B raw37777step1 raw37777step1Labels := by
      have ha : raw37777step1 = (fun i j => raw37777step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37777step1 raw37777step0; decide +kernel
      have hl : raw37777step1Labels = raw37777step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37777step0 raw37777step0Labels permutation34 permutation4
    mixedMoment B raw37777step1 raw37777step1Labels = mixedMoment B raw37777step2 raw37777step2Labels := by
      have ha : raw37777step2 = -raw37777step1 := by apply Matrix.ext; change ∀ i j, raw37777step2 i j = -(raw37777step1 i j); unfold raw37777step2 raw37777step1; decide +kernel
      have hl : raw37777step2Labels = raw37777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2157 node2157Labels := by rfl

def raw37778 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37778 raw37778Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw37778 raw37778Labels = mixedMoment B raw37778step0 raw37778step0Labels := by
      have hz : ∀ j, raw37778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37778step0 = (fun i j => raw37778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37778step0 raw37778; decide +kernel
      have hl : raw37778step0Labels = raw37778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37778 raw37778Labels permutation346 hz
    mixedMoment B raw37778step0 raw37778step0Labels = mixedMoment B raw37778step1 raw37778step1Labels := by
      have ha : raw37778step1 = (fun i j => raw37778step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37778step1 raw37778step0; decide +kernel
      have hl : raw37778step1Labels = raw37778step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37778step0 raw37778step0Labels permutation32 permutation4
    mixedMoment B raw37778step1 raw37778step1Labels = mixedMoment B raw37778step2 raw37778step2Labels := by
      have ha : raw37778step2 = -raw37778step1 := by apply Matrix.ext; change ∀ i j, raw37778step2 i j = -(raw37778step1 i j); unfold raw37778step2 raw37778step1; decide +kernel
      have hl : raw37778step2Labels = raw37778step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2152 node2152Labels := by rfl

def raw37779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw37779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw37779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37779 raw37779Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw37779 raw37779Labels = mixedMoment B raw37779step0 raw37779step0Labels := by
      have hz : ∀ j, raw37779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37779step0 = (fun i j => raw37779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37779step0 raw37779; decide +kernel
      have hl : raw37779step0Labels = raw37779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37779 raw37779Labels permutation346 hz
    mixedMoment B raw37779step0 raw37779step0Labels = mixedMoment B raw37779step1 raw37779step1Labels := by
      have ha : raw37779step1 = (fun i j => raw37779step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37779step1 raw37779step0; decide +kernel
      have hl : raw37779step1Labels = raw37779step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37779step0 raw37779step0Labels permutation32 permutation4
    mixedMoment B raw37779step1 raw37779step1Labels = mixedMoment B raw37779step2 raw37779step2Labels := by
      have ha : raw37779step2 = -raw37779step1 := by apply Matrix.ext; change ∀ i j, raw37779step2 i j = -(raw37779step1 i j); unfold raw37779step2 raw37779step1; decide +kernel
      have hl : raw37779step2Labels = raw37779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2146 node2146Labels := by rfl

def raw37780 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![0, 0], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37780Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37780step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37780step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37780step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw37780step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37780 raw37780Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw37780 raw37780Labels = mixedMoment B raw37780step0 raw37780step0Labels := by
      have hz : ∀ j, raw37780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37780step0 = (fun i j => raw37780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37780step0 raw37780; decide +kernel
      have hl : raw37780step0Labels = raw37780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37780 raw37780Labels permutation346 hz
    mixedMoment B raw37780step0 raw37780step0Labels = mixedMoment B raw37780step1 raw37780step1Labels := by
      have ha : raw37780step1 = -raw37780step0 := by apply Matrix.ext; change ∀ i j, raw37780step1 i j = -(raw37780step0 i j); unfold raw37780step1 raw37780step0; decide +kernel
      have hl : raw37780step1Labels = raw37780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw37781 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw37781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37781 raw37781Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw37781 raw37781Labels = mixedMoment B raw37781step0 raw37781step0Labels := by
      have hz : ∀ j, raw37781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37781step0 = (fun i j => raw37781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37781step0 raw37781; decide +kernel
      have hl : raw37781step0Labels = raw37781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37781 raw37781Labels permutation346 hz
    mixedMoment B raw37781step0 raw37781step0Labels = mixedMoment B raw37781step1 raw37781step1Labels := by
      have ha : raw37781step1 = (fun i j => raw37781step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37781step1 raw37781step0; decide +kernel
      have hl : raw37781step1Labels = raw37781step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37781step0 raw37781step0Labels permutation34 permutation4
    mixedMoment B raw37781step1 raw37781step1Labels = mixedMoment B raw37781step2 raw37781step2Labels := by
      have ha : raw37781step2 = -raw37781step1 := by apply Matrix.ext; change ∀ i j, raw37781step2 i j = -(raw37781step1 i j); unfold raw37781step2 raw37781step1; decide +kernel
      have hl : raw37781step2Labels = raw37781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3595 node3595Labels := by rfl

def raw37782 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37782Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37782 raw37782Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw37782 raw37782Labels = mixedMoment B raw37782step0 raw37782step0Labels := by
      have hz : ∀ j, raw37782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37782step0 = (fun i j => raw37782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37782step0 raw37782; decide +kernel
      have hl : raw37782step0Labels = raw37782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37782 raw37782Labels permutation346 hz
    mixedMoment B raw37782step0 raw37782step0Labels = mixedMoment B raw37782step1 raw37782step1Labels := by
      have ha : raw37782step1 = (fun i j => raw37782step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37782step1 raw37782step0; decide +kernel
      have hl : raw37782step1Labels = raw37782step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37782step0 raw37782step0Labels permutation44 permutation4
    mixedMoment B raw37782step1 raw37782step1Labels = mixedMoment B raw37782step2 raw37782step2Labels := by
      have ha : raw37782step2 = -raw37782step1 := by apply Matrix.ext; change ∀ i j, raw37782step2 i j = -(raw37782step1 i j); unfold raw37782step2 raw37782step1; decide +kernel
      have hl : raw37782step2Labels = raw37782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2272 node2272Labels := by rfl

def raw37783 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37783step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37783 raw37783Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw37783 raw37783Labels = mixedMoment B raw37783step0 raw37783step0Labels := by
      have ha : raw37783step0 = (fun i j => raw37783 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37783step0 raw37783; decide +kernel
      have hl : raw37783step0Labels = raw37783Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37783 raw37783Labels permutation164 permutation4
    mixedMoment B raw37783step0 raw37783step0Labels = mixedMoment B raw37783step1 raw37783step1Labels := by
      have ha : raw37783step1 = -raw37783step0 := by apply Matrix.ext; change ∀ i j, raw37783step1 i j = -(raw37783step0 i j); unfold raw37783step1 raw37783step0; decide +kernel
      have hl : raw37783step1Labels = raw37783step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2154 node2154Labels := by rfl

def raw37784 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -2, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37784 raw37784Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw37784 raw37784Labels = mixedMoment B raw37784step0 raw37784step0Labels := by
      have hz : ∀ j, raw37784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37784step0 = (fun i j => raw37784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37784step0 raw37784; decide +kernel
      have hl : raw37784step0Labels = raw37784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37784 raw37784Labels permutation346 hz
    mixedMoment B raw37784step0 raw37784step0Labels = mixedMoment B raw37784step1 raw37784step1Labels := by
      have ha : raw37784step1 = (fun i j => raw37784step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37784step1 raw37784step0; decide +kernel
      have hl : raw37784step1Labels = raw37784step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37784step0 raw37784step0Labels permutation35 permutation4
    mixedMoment B raw37784step1 raw37784step1Labels = mixedMoment B raw37784step2 raw37784step2Labels := by
      have ha : raw37784step2 = -raw37784step1 := by apply Matrix.ext; change ∀ i j, raw37784step2 i j = -(raw37784step1 i j); unfold raw37784step2 raw37784step1; decide +kernel
      have hl : raw37784step2Labels = raw37784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2158 node2158Labels := by rfl

def raw37785 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37785 raw37785Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw37785 raw37785Labels = mixedMoment B raw37785step0 raw37785step0Labels := by
      have hz : ∀ j, raw37785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37785step0 = (fun i j => raw37785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37785step0 raw37785; decide +kernel
      have hl : raw37785step0Labels = raw37785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37785 raw37785Labels permutation346 hz
    mixedMoment B raw37785step0 raw37785step0Labels = mixedMoment B raw37785step1 raw37785step1Labels := by
      have ha : raw37785step1 = (fun i j => raw37785step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37785step1 raw37785step0; decide +kernel
      have hl : raw37785step1Labels = raw37785step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37785step0 raw37785step0Labels permutation32 permutation4
    mixedMoment B raw37785step1 raw37785step1Labels = mixedMoment B raw37785step2 raw37785step2Labels := by
      have ha : raw37785step2 = -raw37785step1 := by apply Matrix.ext; change ∀ i j, raw37785step2 i j = -(raw37785step1 i j); unfold raw37785step2 raw37785step1; decide +kernel
      have hl : raw37785step2Labels = raw37785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2166 node2166Labels := by rfl

def raw37786 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37786 raw37786Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw37786 raw37786Labels = mixedMoment B raw37786step0 raw37786step0Labels := by
      have hz : ∀ j, raw37786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37786step0 = (fun i j => raw37786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37786step0 raw37786; decide +kernel
      have hl : raw37786step0Labels = raw37786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37786 raw37786Labels permutation346 hz
    mixedMoment B raw37786step0 raw37786step0Labels = mixedMoment B raw37786step1 raw37786step1Labels := by
      have ha : raw37786step1 = (fun i j => raw37786step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37786step1 raw37786step0; decide +kernel
      have hl : raw37786step1Labels = raw37786step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37786step0 raw37786step0Labels permutation32 permutation4
    mixedMoment B raw37786step1 raw37786step1Labels = mixedMoment B raw37786step2 raw37786step2Labels := by
      have ha : raw37786step2 = -raw37786step1 := by apply Matrix.ext; change ∀ i j, raw37786step2 i j = -(raw37786step1 i j); unfold raw37786step2 raw37786step1; decide +kernel
      have hl : raw37786step2Labels = raw37786step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3592 node3592Labels := by rfl

def raw37787 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw37787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw37787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37787 raw37787Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw37787 raw37787Labels = mixedMoment B raw37787step0 raw37787step0Labels := by
      have hz : ∀ j, raw37787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37787step0 = (fun i j => raw37787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37787step0 raw37787; decide +kernel
      have hl : raw37787step0Labels = raw37787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37787 raw37787Labels permutation346 hz
    mixedMoment B raw37787step0 raw37787step0Labels = mixedMoment B raw37787step1 raw37787step1Labels := by
      have ha : raw37787step1 = (fun i j => raw37787step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37787step1 raw37787step0; decide +kernel
      have hl : raw37787step1Labels = raw37787step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37787step0 raw37787step0Labels permutation38 permutation4
    mixedMoment B raw37787step1 raw37787step1Labels = mixedMoment B raw37787step2 raw37787step2Labels := by
      have ha : raw37787step2 = -raw37787step1 := by apply Matrix.ext; change ∀ i j, raw37787step2 i j = -(raw37787step1 i j); unfold raw37787step2 raw37787step1; decide +kernel
      have hl : raw37787step2Labels = raw37787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2257 node2257Labels := by rfl

def raw37788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw37788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw37788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37788 raw37788Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw37788 raw37788Labels = mixedMoment B raw37788step0 raw37788step0Labels := by
      have ha : raw37788step0 = (fun i j => raw37788 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37788step0 raw37788; decide +kernel
      have hl : raw37788step0Labels = raw37788Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37788 raw37788Labels permutation158 permutation4
    mixedMoment B raw37788step0 raw37788step0Labels = mixedMoment B raw37788step1 raw37788step1Labels := by
      have ha : raw37788step1 = -raw37788step0 := by apply Matrix.ext; change ∀ i j, raw37788step1 i j = -(raw37788step0 i j); unfold raw37788step1 raw37788step0; decide +kernel
      have hl : raw37788step1Labels = raw37788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2148 node2148Labels := by rfl

def raw37789 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37789 raw37789Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw37789 raw37789Labels = mixedMoment B raw37789step0 raw37789step0Labels := by
      have hz : ∀ j, raw37789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37789step0 = (fun i j => raw37789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37789step0 raw37789; decide +kernel
      have hl : raw37789step0Labels = raw37789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37789 raw37789Labels permutation346 hz
    mixedMoment B raw37789step0 raw37789step0Labels = mixedMoment B raw37789step1 raw37789step1Labels := by
      have ha : raw37789step1 = (fun i j => raw37789step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37789step1 raw37789step0; decide +kernel
      have hl : raw37789step1Labels = raw37789step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37789step0 raw37789step0Labels permutation33 permutation4
    mixedMoment B raw37789step1 raw37789step1Labels = mixedMoment B raw37789step2 raw37789step2Labels := by
      have ha : raw37789step2 = -raw37789step1 := by apply Matrix.ext; change ∀ i j, raw37789step2 i j = -(raw37789step1 i j); unfold raw37789step2 raw37789step1; decide +kernel
      have hl : raw37789step2Labels = raw37789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2152 node2152Labels := by rfl

def raw37790 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37790 raw37790Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw37790 raw37790Labels = mixedMoment B raw37790step0 raw37790step0Labels := by
      have hz : ∀ j, raw37790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37790step0 = (fun i j => raw37790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37790step0 raw37790; decide +kernel
      have hl : raw37790step0Labels = raw37790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37790 raw37790Labels permutation346 hz
    mixedMoment B raw37790step0 raw37790step0Labels = mixedMoment B raw37790step1 raw37790step1Labels := by
      have ha : raw37790step1 = (fun i j => raw37790step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37790step1 raw37790step0; decide +kernel
      have hl : raw37790step1Labels = raw37790step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37790step0 raw37790step0Labels permutation36 permutation2
    mixedMoment B raw37790step1 raw37790step1Labels = mixedMoment B raw37790step2 raw37790step2Labels := by
      have ha : raw37790step2 = -raw37790step1 := by apply Matrix.ext; change ∀ i j, raw37790step2 i j = -(raw37790step1 i j); unfold raw37790step2 raw37790step1; decide +kernel
      have hl : raw37790step2Labels = raw37790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3417 node3417Labels := by rfl

def raw37791 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw37791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37791 raw37791Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw37791 raw37791Labels = mixedMoment B raw37791step0 raw37791step0Labels := by
      have ha : raw37791step0 = (fun i j => raw37791 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37791step0 raw37791; decide +kernel
      have hl : raw37791step0Labels = raw37791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37791 raw37791Labels permutation160 permutation4
    mixedMoment B raw37791step0 raw37791step0Labels = mixedMoment B raw37791step1 raw37791step1Labels := by
      have ha : raw37791step1 = -raw37791step0 := by apply Matrix.ext; change ∀ i j, raw37791step1 i j = -(raw37791step0 i j); unfold raw37791step1 raw37791step0; decide +kernel
      have hl : raw37791step1Labels = raw37791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw37792 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37792 raw37792Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw37792 raw37792Labels = mixedMoment B raw37792step0 raw37792step0Labels := by
      have hz : ∀ j, raw37792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37792step0 = (fun i j => raw37792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37792step0 raw37792; decide +kernel
      have hl : raw37792step0Labels = raw37792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37792 raw37792Labels permutation346 hz
    mixedMoment B raw37792step0 raw37792step0Labels = mixedMoment B raw37792step1 raw37792step1Labels := by
      have ha : raw37792step1 = (fun i j => raw37792step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37792step1 raw37792step0; decide +kernel
      have hl : raw37792step1Labels = raw37792step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37792step0 raw37792step0Labels permutation34 permutation4
    mixedMoment B raw37792step1 raw37792step1Labels = mixedMoment B raw37792step2 raw37792step2Labels := by
      have ha : raw37792step2 = -raw37792step1 := by apply Matrix.ext; change ∀ i j, raw37792step2 i j = -(raw37792step1 i j); unfold raw37792step2 raw37792step1; decide +kernel
      have hl : raw37792step2Labels = raw37792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3417 node3417Labels := by rfl

def raw37793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37793 raw37793Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw37793 raw37793Labels = mixedMoment B raw37793step0 raw37793step0Labels := by
      have hz : ∀ j, raw37793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37793step0 = (fun i j => raw37793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37793step0 raw37793; decide +kernel
      have hl : raw37793step0Labels = raw37793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37793 raw37793Labels permutation346 hz
    mixedMoment B raw37793step0 raw37793step0Labels = mixedMoment B raw37793step1 raw37793step1Labels := by
      have ha : raw37793step1 = (fun i j => raw37793step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37793step1 raw37793step0; decide +kernel
      have hl : raw37793step1Labels = raw37793step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37793step0 raw37793step0Labels permutation32 permutation4
    mixedMoment B raw37793step1 raw37793step1Labels = mixedMoment B raw37793step2 raw37793step2Labels := by
      have ha : raw37793step2 = -raw37793step1 := by apply Matrix.ext; change ∀ i j, raw37793step2 i j = -(raw37793step1 i j); unfold raw37793step2 raw37793step1; decide +kernel
      have hl : raw37793step2Labels = raw37793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw37794 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37794 raw37794Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw37794 raw37794Labels = mixedMoment B raw37794step0 raw37794step0Labels := by
      have hz : ∀ j, raw37794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37794step0 = (fun i j => raw37794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37794step0 raw37794; decide +kernel
      have hl : raw37794step0Labels = raw37794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37794 raw37794Labels permutation346 hz
    mixedMoment B raw37794step0 raw37794step0Labels = mixedMoment B raw37794step1 raw37794step1Labels := by
      have ha : raw37794step1 = (fun i j => raw37794step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37794step1 raw37794step0; decide +kernel
      have hl : raw37794step1Labels = raw37794step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37794step0 raw37794step0Labels permutation151 permutation4
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw37795 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37795 raw37795Labels = mixedMoment B node1848 node1848Labels := by
  calc
    mixedMoment B raw37795 raw37795Labels = mixedMoment B raw37795step0 raw37795step0Labels := by
      have ha : raw37795step0 = (fun i j => raw37795 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37795step0 raw37795; decide +kernel
      have hl : raw37795step0Labels = raw37795Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37795 raw37795Labels permutation152 permutation4
    mixedMoment B raw37795step0 raw37795step0Labels = mixedMoment B raw37795step1 raw37795step1Labels := by
      have ha : raw37795step1 = -raw37795step0 := by apply Matrix.ext; change ∀ i j, raw37795step1 i j = -(raw37795step0 i j); unfold raw37795step1 raw37795step0; decide +kernel
      have hl : raw37795step1Labels = raw37795step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1848 node1848Labels := by rfl

def raw37796 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37796 raw37796Labels = mixedMoment B node3324 node3324Labels := by
  calc
    mixedMoment B raw37796 raw37796Labels = mixedMoment B raw37796step0 raw37796step0Labels := by
      have ha : raw37796step0 = (fun i j => raw37796 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37796step0 raw37796; decide +kernel
      have hl : raw37796step0Labels = raw37796Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37796 raw37796Labels permutation152 permutation4
    mixedMoment B raw37796step0 raw37796step0Labels = mixedMoment B raw37796step1 raw37796step1Labels := by
      have ha : raw37796step1 = -raw37796step0 := by apply Matrix.ext; change ∀ i j, raw37796step1 i j = -(raw37796step0 i j); unfold raw37796step1 raw37796step0; decide +kernel
      have hl : raw37796step1Labels = raw37796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3324 node3324Labels := by rfl

def raw37797 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37797step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37797 raw37797Labels = mixedMoment B node3421 node3421Labels := by
  calc
    mixedMoment B raw37797 raw37797Labels = mixedMoment B raw37797step0 raw37797step0Labels := by
      have hz : ∀ j, raw37797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37797step0 = (fun i j => raw37797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37797step0 raw37797; decide +kernel
      have hl : raw37797step0Labels = raw37797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37797 raw37797Labels permutation346 hz
    mixedMoment B raw37797step0 raw37797step0Labels = mixedMoment B raw37797step1 raw37797step1Labels := by
      have ha : raw37797step1 = (fun i j => raw37797step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37797step1 raw37797step0; decide +kernel
      have hl : raw37797step1Labels = raw37797step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37797step0 raw37797step0Labels permutation32 permutation4
    mixedMoment B raw37797step1 raw37797step1Labels = mixedMoment B raw37797step2 raw37797step2Labels := by
      have ha : raw37797step2 = -raw37797step1 := by apply Matrix.ext; change ∀ i j, raw37797step2 i j = -(raw37797step1 i j); unfold raw37797step2 raw37797step1; decide +kernel
      have hl : raw37797step2Labels = raw37797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3421 node3421Labels := by rfl

def raw37798 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw37798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw37798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37798 raw37798Labels = mixedMoment B node3409 node3409Labels := by
  calc
    mixedMoment B raw37798 raw37798Labels = mixedMoment B raw37798step0 raw37798step0Labels := by
      have ha : raw37798step0 = (fun i j => raw37798 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37798step0 raw37798; decide +kernel
      have hl : raw37798step0Labels = raw37798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37798 raw37798Labels permutation158 permutation4
    mixedMoment B raw37798step0 raw37798step0Labels = mixedMoment B raw37798step1 raw37798step1Labels := by
      have ha : raw37798step1 = -raw37798step0 := by apply Matrix.ext; change ∀ i j, raw37798step1 i j = -(raw37798step0 i j); unfold raw37798step1 raw37798step0; decide +kernel
      have hl : raw37798step1Labels = raw37798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3409 node3409Labels := by rfl

def raw37799 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37799step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37799 raw37799Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw37799 raw37799Labels = mixedMoment B raw37799step0 raw37799step0Labels := by
      have ha : raw37799step0 = (fun i j => raw37799 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37799step0 raw37799; decide +kernel
      have hl : raw37799step0Labels = raw37799Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37799 raw37799Labels permutation164 permutation4
    mixedMoment B raw37799step0 raw37799step0Labels = mixedMoment B raw37799step1 raw37799step1Labels := by
      have ha : raw37799step1 = -raw37799step0 := by apply Matrix.ext; change ∀ i j, raw37799step1 i j = -(raw37799step0 i j); unfold raw37799step1 raw37799step0; decide +kernel
      have hl : raw37799step1Labels = raw37799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw37800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37800 raw37800Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw37800 raw37800Labels = mixedMoment B raw37800step0 raw37800step0Labels := by
      have ha : raw37800step0 = (fun i j => raw37800 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37800step0 raw37800; decide +kernel
      have hl : raw37800step0Labels = raw37800Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37800 raw37800Labels permutation170 permutation4
    mixedMoment B raw37800step0 raw37800step0Labels = mixedMoment B raw37800step1 raw37800step1Labels := by
      have ha : raw37800step1 = -raw37800step0 := by apply Matrix.ext; change ∀ i j, raw37800step1 i j = -(raw37800step0 i j); unfold raw37800step1 raw37800step0; decide +kernel
      have hl : raw37800step1Labels = raw37800step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw37801 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw37801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37801 raw37801Labels = mixedMoment B node3320 node3320Labels := by
  calc
    mixedMoment B raw37801 raw37801Labels = mixedMoment B raw37801step0 raw37801step0Labels := by
      have ha : raw37801step0 = (fun i j => raw37801 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37801step0 raw37801; decide +kernel
      have hl : raw37801step0Labels = raw37801Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37801 raw37801Labels permutation170 permutation2
    mixedMoment B raw37801step0 raw37801step0Labels = mixedMoment B raw37801step1 raw37801step1Labels := by
      have ha : raw37801step1 = -raw37801step0 := by apply Matrix.ext; change ∀ i j, raw37801step1 i j = -(raw37801step0 i j); unfold raw37801step1 raw37801step0; decide +kernel
      have hl : raw37801step1Labels = raw37801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3320 node3320Labels := by rfl

def raw37802 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-2, 1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw37802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw37802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37802 raw37802Labels = mixedMoment B node3322 node3322Labels := by
  calc
    mixedMoment B raw37802 raw37802Labels = mixedMoment B raw37802step0 raw37802step0Labels := by
      have hz : ∀ j, raw37802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37802step0 = (fun i j => raw37802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37802step0 raw37802; decide +kernel
      have hl : raw37802step0Labels = raw37802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37802 raw37802Labels permutation346 hz
    mixedMoment B raw37802step0 raw37802step0Labels = mixedMoment B raw37802step1 raw37802step1Labels := by
      have ha : raw37802step1 = (fun i j => raw37802step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37802step1 raw37802step0; decide +kernel
      have hl : raw37802step1Labels = raw37802step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37802step0 raw37802step0Labels permutation36 permutation2
    mixedMoment B raw37802step1 raw37802step1Labels = mixedMoment B raw37802step2 raw37802step2Labels := by
      have ha : raw37802step2 = -raw37802step1 := by apply Matrix.ext; change ∀ i j, raw37802step2 i j = -(raw37802step1 i j); unfold raw37802step2 raw37802step1; decide +kernel
      have hl : raw37802step2Labels = raw37802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3322 node3322Labels := by rfl

def raw37803 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-3, 1, 2], ![0, -2, 2]]
def raw37803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-3, 1, 2], ![0, -2, 2]]
def raw37803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw37803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37803 raw37803Labels = mixedMoment B node2447 node2447Labels := by
  calc
    mixedMoment B raw37803 raw37803Labels = mixedMoment B raw37803step0 raw37803step0Labels := by
      have hz : ∀ j, raw37803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37803step0 = (fun i j => raw37803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37803step0 raw37803; decide +kernel
      have hl : raw37803step0Labels = raw37803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37803 raw37803Labels permutation346 hz
    mixedMoment B raw37803step0 raw37803step0Labels = mixedMoment B raw37803step1 raw37803step1Labels := by
      have ha : raw37803step1 = (fun i j => raw37803step0 (permutation121 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37803step1 raw37803step0; decide +kernel
      have hl : raw37803step1Labels = raw37803step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37803step0 raw37803step0Labels permutation121 permutation2
    _ = mixedMoment B node2447 node2447Labels := by rfl

def raw37804 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37804 raw37804Labels = mixedMoment B node3328 node3328Labels := by
  calc
    mixedMoment B raw37804 raw37804Labels = mixedMoment B raw37804step0 raw37804step0Labels := by
      have hz : ∀ j, raw37804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37804step0 = (fun i j => raw37804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37804step0 raw37804; decide +kernel
      have hl : raw37804step0Labels = raw37804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37804 raw37804Labels permutation346 hz
    mixedMoment B raw37804step0 raw37804step0Labels = mixedMoment B raw37804step1 raw37804step1Labels := by
      have ha : raw37804step1 = (fun i j => raw37804step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37804step1 raw37804step0; decide +kernel
      have hl : raw37804step1Labels = raw37804step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37804step0 raw37804step0Labels permutation33 permutation2
    mixedMoment B raw37804step1 raw37804step1Labels = mixedMoment B raw37804step2 raw37804step2Labels := by
      have ha : raw37804step2 = -raw37804step1 := by apply Matrix.ext; change ∀ i j, raw37804step2 i j = -(raw37804step1 i j); unfold raw37804step2 raw37804step1; decide +kernel
      have hl : raw37804step2Labels = raw37804step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3328 node3328Labels := by rfl

def raw37805 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![-1, 0, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37805 raw37805Labels = mixedMoment B node2368 node2368Labels := by
  calc
    mixedMoment B raw37805 raw37805Labels = mixedMoment B raw37805step0 raw37805step0Labels := by
      have hz : ∀ j, raw37805 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37805step0 = (fun i j => raw37805 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37805step0 raw37805; decide +kernel
      have hl : raw37805step0Labels = raw37805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37805 raw37805Labels permutation346 hz
    mixedMoment B raw37805step0 raw37805step0Labels = mixedMoment B raw37805step1 raw37805step1Labels := by
      have ha : raw37805step1 = (fun i j => raw37805step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37805step1 raw37805step0; decide +kernel
      have hl : raw37805step1Labels = raw37805step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37805step0 raw37805step0Labels permutation57 permutation2
    mixedMoment B raw37805step1 raw37805step1Labels = mixedMoment B raw37805step2 raw37805step2Labels := by
      have ha : raw37805step2 = -raw37805step1 := by apply Matrix.ext; change ∀ i j, raw37805step2 i j = -(raw37805step1 i j); unfold raw37805step2 raw37805step1; decide +kernel
      have hl : raw37805step2Labels = raw37805step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2368 node2368Labels := by rfl

def raw37806 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw37806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw37806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37806 raw37806Labels = mixedMoment B node3589 node3589Labels := by
  calc
    mixedMoment B raw37806 raw37806Labels = mixedMoment B raw37806step0 raw37806step0Labels := by
      have ha : raw37806step0 = (fun i j => raw37806 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37806step0 raw37806; decide +kernel
      have hl : raw37806step0Labels = raw37806Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37806 raw37806Labels permutation160 permutation4
    mixedMoment B raw37806step0 raw37806step0Labels = mixedMoment B raw37806step1 raw37806step1Labels := by
      have ha : raw37806step1 = -raw37806step0 := by apply Matrix.ext; change ∀ i j, raw37806step1 i j = -(raw37806step0 i j); unfold raw37806step1 raw37806step0; decide +kernel
      have hl : raw37806step1Labels = raw37806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3589 node3589Labels := by rfl

def raw37807 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37807 raw37807Labels = mixedMoment B node3421 node3421Labels := by
  calc
    mixedMoment B raw37807 raw37807Labels = mixedMoment B raw37807step0 raw37807step0Labels := by
      have hz : ∀ j, raw37807 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37807step0 = (fun i j => raw37807 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37807step0 raw37807; decide +kernel
      have hl : raw37807step0Labels = raw37807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37807 raw37807Labels permutation346 hz
    mixedMoment B raw37807step0 raw37807step0Labels = mixedMoment B raw37807step1 raw37807step1Labels := by
      have ha : raw37807step1 = -raw37807step0 := by apply Matrix.ext; change ∀ i j, raw37807step1 i j = -(raw37807step0 i j); unfold raw37807step1 raw37807step0; decide +kernel
      have hl : raw37807step1Labels = raw37807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3421 node3421Labels := by rfl

def raw37808 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37808 raw37808Labels = mixedMoment B node3324 node3324Labels := by
  calc
    mixedMoment B raw37808 raw37808Labels = mixedMoment B raw37808step0 raw37808step0Labels := by
      have ha : raw37808step0 = -raw37808 := by apply Matrix.ext; change ∀ i j, raw37808step0 i j = -(raw37808 i j); unfold raw37808step0 raw37808; decide +kernel
      have hl : raw37808step0Labels = raw37808Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3324 node3324Labels := by rfl

def raw37809 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-2, 1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37809 raw37809Labels = mixedMoment B node3330 node3330Labels := by
  calc
    mixedMoment B raw37809 raw37809Labels = mixedMoment B raw37809step0 raw37809step0Labels := by
      have hz : ∀ j, raw37809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37809step0 = (fun i j => raw37809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37809step0 raw37809; decide +kernel
      have hl : raw37809step0Labels = raw37809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37809 raw37809Labels permutation346 hz
    mixedMoment B raw37809step0 raw37809step0Labels = mixedMoment B raw37809step1 raw37809step1Labels := by
      have ha : raw37809step1 = (fun i j => raw37809step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37809step1 raw37809step0; decide +kernel
      have hl : raw37809step1Labels = raw37809step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37809step0 raw37809step0Labels permutation35 permutation2
    mixedMoment B raw37809step1 raw37809step1Labels = mixedMoment B raw37809step2 raw37809step2Labels := by
      have ha : raw37809step2 = -raw37809step1 := by apply Matrix.ext; change ∀ i j, raw37809step2 i j = -(raw37809step1 i j); unfold raw37809step2 raw37809step1; decide +kernel
      have hl : raw37809step2Labels = raw37809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3330 node3330Labels := by rfl

def raw37810 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37810step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37810 raw37810Labels = mixedMoment B node3328 node3328Labels := by
  calc
    mixedMoment B raw37810 raw37810Labels = mixedMoment B raw37810step0 raw37810step0Labels := by
      have hz : ∀ j, raw37810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37810step0 = (fun i j => raw37810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37810step0 raw37810; decide +kernel
      have hl : raw37810step0Labels = raw37810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37810 raw37810Labels permutation346 hz
    mixedMoment B raw37810step0 raw37810step0Labels = mixedMoment B raw37810step1 raw37810step1Labels := by
      have ha : raw37810step1 = -raw37810step0 := by apply Matrix.ext; change ∀ i j, raw37810step1 i j = -(raw37810step0 i j); unfold raw37810step1 raw37810step0; decide +kernel
      have hl : raw37810step1Labels = raw37810step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3328 node3328Labels := by rfl

def raw37811 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37811 raw37811Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw37811 raw37811Labels = mixedMoment B raw37811step0 raw37811step0Labels := by
      have hz : ∀ j, raw37811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37811step0 = (fun i j => raw37811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37811step0 raw37811; decide +kernel
      have hl : raw37811step0Labels = raw37811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37811 raw37811Labels permutation346 hz
    mixedMoment B raw37811step0 raw37811step0Labels = mixedMoment B raw37811step1 raw37811step1Labels := by
      have ha : raw37811step1 = (fun i j => raw37811step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37811step1 raw37811step0; decide +kernel
      have hl : raw37811step1Labels = raw37811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37811step0 raw37811step0Labels permutation33 permutation2
    mixedMoment B raw37811step1 raw37811step1Labels = mixedMoment B raw37811step2 raw37811step2Labels := by
      have ha : raw37811step2 = -raw37811step1 := by apply Matrix.ext; change ∀ i j, raw37811step2 i j = -(raw37811step1 i j); unfold raw37811step2 raw37811step1; decide +kernel
      have hl : raw37811step2Labels = raw37811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw37812 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw37812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37812 raw37812Labels = mixedMoment B node3316 node3316Labels := by
  calc
    mixedMoment B raw37812 raw37812Labels = mixedMoment B raw37812step0 raw37812step0Labels := by
      have ha : raw37812step0 = (fun i j => raw37812 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37812step0 raw37812; decide +kernel
      have hl : raw37812step0Labels = raw37812Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37812 raw37812Labels permutation159 permutation2
    mixedMoment B raw37812step0 raw37812step0Labels = mixedMoment B raw37812step1 raw37812step1Labels := by
      have ha : raw37812step1 = -raw37812step0 := by apply Matrix.ext; change ∀ i j, raw37812step1 i j = -(raw37812step0 i j); unfold raw37812step1 raw37812step0; decide +kernel
      have hl : raw37812step1Labels = raw37812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3316 node3316Labels := by rfl

def raw37813 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2], ![-1, -1, 2]]
def raw37813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-3, 1, 2], ![-1, -1, 2]]
def raw37813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37813 raw37813Labels = mixedMoment B node2376 node2376Labels := by
  calc
    mixedMoment B raw37813 raw37813Labels = mixedMoment B raw37813step0 raw37813step0Labels := by
      have hz : ∀ j, raw37813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37813step0 = (fun i j => raw37813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37813step0 raw37813; decide +kernel
      have hl : raw37813step0Labels = raw37813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37813 raw37813Labels permutation346 hz
    mixedMoment B raw37813step0 raw37813step0Labels = mixedMoment B raw37813step1 raw37813step1Labels := by
      have ha : raw37813step1 = (fun i j => raw37813step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37813step1 raw37813step0; decide +kernel
      have hl : raw37813step1Labels = raw37813step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37813step0 raw37813step0Labels permutation127 permutation2
    _ = mixedMoment B node2376 node2376Labels := by rfl

def raw37814 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw37814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37814 raw37814Labels = mixedMoment B node3319 node3319Labels := by
  calc
    mixedMoment B raw37814 raw37814Labels = mixedMoment B raw37814step0 raw37814step0Labels := by
      have hz : ∀ j, raw37814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37814step0 = (fun i j => raw37814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37814step0 raw37814; decide +kernel
      have hl : raw37814step0Labels = raw37814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37814 raw37814Labels permutation346 hz
    mixedMoment B raw37814step0 raw37814step0Labels = mixedMoment B raw37814step1 raw37814step1Labels := by
      have ha : raw37814step1 = -raw37814step0 := by apply Matrix.ext; change ∀ i j, raw37814step1 i j = -(raw37814step0 i j); unfold raw37814step1 raw37814step0; decide +kernel
      have hl : raw37814step1Labels = raw37814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3319 node3319Labels := by rfl

def raw37815 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw37815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37815 raw37815Labels = mixedMoment B node2365 node2365Labels := by
  calc
    mixedMoment B raw37815 raw37815Labels = mixedMoment B raw37815step0 raw37815step0Labels := by
      have hz : ∀ j, raw37815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37815step0 = (fun i j => raw37815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37815step0 raw37815; decide +kernel
      have hl : raw37815step0Labels = raw37815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37815 raw37815Labels permutation346 hz
    mixedMoment B raw37815step0 raw37815step0Labels = mixedMoment B raw37815step1 raw37815step1Labels := by
      have ha : raw37815step1 = (fun i j => raw37815step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37815step1 raw37815step0; decide +kernel
      have hl : raw37815step1Labels = raw37815step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37815step0 raw37815step0Labels permutation56 permutation2
    mixedMoment B raw37815step1 raw37815step1Labels = mixedMoment B raw37815step2 raw37815step2Labels := by
      have ha : raw37815step2 = -raw37815step1 := by apply Matrix.ext; change ∀ i j, raw37815step2 i j = -(raw37815step1 i j); unfold raw37815step2 raw37815step1; decide +kernel
      have hl : raw37815step2Labels = raw37815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2365 node2365Labels := by rfl

def raw37816 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw37816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw37816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37816 raw37816Labels = mixedMoment B node3593 node3593Labels := by
  calc
    mixedMoment B raw37816 raw37816Labels = mixedMoment B raw37816step0 raw37816step0Labels := by
      have ha : raw37816step0 = (fun i j => raw37816 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37816step0 raw37816; decide +kernel
      have hl : raw37816step0Labels = raw37816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37816 raw37816Labels permutation168 permutation4
    mixedMoment B raw37816step0 raw37816step0Labels = mixedMoment B raw37816step1 raw37816step1Labels := by
      have ha : raw37816step1 = -raw37816step0 := by apply Matrix.ext; change ∀ i j, raw37816step1 i j = -(raw37816step0 i j); unfold raw37816step1 raw37816step0; decide +kernel
      have hl : raw37816step1Labels = raw37816step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3593 node3593Labels := by rfl

def raw37817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![0, -2, 2], ![-2, 1, 1]]
def raw37817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw37817step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37817 raw37817Labels = mixedMoment B node3594 node3594Labels := by
  calc
    mixedMoment B raw37817 raw37817Labels = mixedMoment B raw37817step0 raw37817step0Labels := by
      have hz : ∀ j, raw37817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37817step0 = (fun i j => raw37817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37817step0 raw37817; decide +kernel
      have hl : raw37817step0Labels = raw37817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37817 raw37817Labels permutation346 hz
    mixedMoment B raw37817step0 raw37817step0Labels = mixedMoment B raw37817step1 raw37817step1Labels := by
      have ha : raw37817step1 = (fun i j => raw37817step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37817step1 raw37817step0; decide +kernel
      have hl : raw37817step1Labels = raw37817step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37817step0 raw37817step0Labels permutation35 permutation4
    mixedMoment B raw37817step1 raw37817step1Labels = mixedMoment B raw37817step2 raw37817step2Labels := by
      have ha : raw37817step2 = -raw37817step1 := by apply Matrix.ext; change ∀ i j, raw37817step2 i j = -(raw37817step1 i j); unfold raw37817step2 raw37817step1; decide +kernel
      have hl : raw37817step2Labels = raw37817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3594 node3594Labels := by rfl

def raw37818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw37818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37818 raw37818Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw37818 raw37818Labels = mixedMoment B raw37818step0 raw37818step0Labels := by
      have hz : ∀ j, raw37818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37818step0 = (fun i j => raw37818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37818step0 raw37818; decide +kernel
      have hl : raw37818step0Labels = raw37818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37818 raw37818Labels permutation346 hz
    mixedMoment B raw37818step0 raw37818step0Labels = mixedMoment B raw37818step1 raw37818step1Labels := by
      have ha : raw37818step1 = (fun i j => raw37818step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37818step1 raw37818step0; decide +kernel
      have hl : raw37818step1Labels = raw37818step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37818step0 raw37818step0Labels permutation36 permutation4
    mixedMoment B raw37818step1 raw37818step1Labels = mixedMoment B raw37818step2 raw37818step2Labels := by
      have ha : raw37818step2 = -raw37818step1 := by apply Matrix.ext; change ∀ i j, raw37818step2 i j = -(raw37818step1 i j); unfold raw37818step2 raw37818step1; decide +kernel
      have hl : raw37818step2Labels = raw37818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3595 node3595Labels := by rfl

def raw37819 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37819 raw37819Labels = mixedMoment B node2182 node2182Labels := by
  calc
    mixedMoment B raw37819 raw37819Labels = mixedMoment B raw37819step0 raw37819step0Labels := by
      have ha : raw37819step0 = (fun i j => raw37819 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37819step0 raw37819; decide +kernel
      have hl : raw37819step0Labels = raw37819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37819 raw37819Labels permutation152 permutation4
    mixedMoment B raw37819step0 raw37819step0Labels = mixedMoment B raw37819step1 raw37819step1Labels := by
      have ha : raw37819step1 = -raw37819step0 := by apply Matrix.ext; change ∀ i j, raw37819step1 i j = -(raw37819step0 i j); unfold raw37819step1 raw37819step0; decide +kernel
      have hl : raw37819step1Labels = raw37819step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2182 node2182Labels := by rfl

def raw37820 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37820 raw37820Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw37820 raw37820Labels = mixedMoment B raw37820step0 raw37820step0Labels := by
      have ha : raw37820step0 = (fun i j => raw37820 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37820step0 raw37820; decide +kernel
      have hl : raw37820step0Labels = raw37820Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37820 raw37820Labels permutation152 permutation4
    mixedMoment B raw37820step0 raw37820step0Labels = mixedMoment B raw37820step1 raw37820step1Labels := by
      have ha : raw37820step1 = -raw37820step0 := by apply Matrix.ext; change ∀ i j, raw37820step1 i j = -(raw37820step0 i j); unfold raw37820step1 raw37820step0; decide +kernel
      have hl : raw37820step1Labels = raw37820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3455 node3455Labels := by rfl

def raw37821 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37821step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37821 raw37821Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw37821 raw37821Labels = mixedMoment B raw37821step0 raw37821step0Labels := by
      have ha : raw37821step0 = (fun i j => raw37821 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37821step0 raw37821; decide +kernel
      have hl : raw37821step0Labels = raw37821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37821 raw37821Labels permutation176 permutation4
    mixedMoment B raw37821step0 raw37821step0Labels = mixedMoment B raw37821step1 raw37821step1Labels := by
      have ha : raw37821step1 = -raw37821step0 := by apply Matrix.ext; change ∀ i j, raw37821step1 i j = -(raw37821step0 i j); unfold raw37821step1 raw37821step0; decide +kernel
      have hl : raw37821step1Labels = raw37821step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3455 node3455Labels := by rfl

def raw37822 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37822 raw37822Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw37822 raw37822Labels = mixedMoment B raw37822step0 raw37822step0Labels := by
      have ha : raw37822step0 = (fun i j => raw37822 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37822step0 raw37822; decide +kernel
      have hl : raw37822step0Labels = raw37822Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37822 raw37822Labels permutation662 permutation2
    _ = mixedMoment B node3455 node3455Labels := by rfl

def raw37823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37823 raw37823Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw37823 raw37823Labels = mixedMoment B raw37823step0 raw37823step0Labels := by
      have ha : raw37823step0 = (fun i j => raw37823 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37823step0 raw37823; decide +kernel
      have hl : raw37823step0Labels = raw37823Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37823 raw37823Labels permutation686 permutation2
    _ = mixedMoment B node3455 node3455Labels := by rfl

def raw37824 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37824 raw37824Labels = mixedMoment B node2182 node2182Labels := by
  calc
    mixedMoment B raw37824 raw37824Labels = mixedMoment B raw37824step0 raw37824step0Labels := by
      have ha : raw37824step0 = (fun i j => raw37824 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37824step0 raw37824; decide +kernel
      have hl : raw37824step0Labels = raw37824Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37824 raw37824Labels permutation662 permutation2
    _ = mixedMoment B node2182 node2182Labels := by rfl

def raw37825 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37825Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37825step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw37825step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37825 raw37825Labels = mixedMoment B node4077 node4077Labels := by
  calc
    mixedMoment B raw37825 raw37825Labels = mixedMoment B raw37825step0 raw37825step0Labels := by
      have ha : raw37825step0 = (fun i j => raw37825 (permutation662 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37825step0 raw37825; decide +kernel
      have hl : raw37825step0Labels = raw37825Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37825 raw37825Labels permutation662 permutation0
    _ = mixedMoment B node4077 node4077Labels := by rfl

def raw37826 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37826Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37826step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37826 raw37826Labels = mixedMoment B node26 node26Labels := by
  calc
    mixedMoment B raw37826 raw37826Labels = mixedMoment B raw37826step0 raw37826step0Labels := by
      have ha : raw37826step0 = (fun i j => raw37826 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37826step0 raw37826; decide +kernel
      have hl : raw37826step0Labels = raw37826Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37826 raw37826Labels permutation44 permutation3
    _ = mixedMoment B node26 node26Labels := by rfl

def raw37827 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37827Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37827step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37827step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37827 raw37827Labels = mixedMoment B node31 node31Labels := by
  calc
    mixedMoment B raw37827 raw37827Labels = mixedMoment B raw37827step0 raw37827step0Labels := by
      have ha : raw37827step0 = (fun i j => raw37827 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37827step0 raw37827; decide +kernel
      have hl : raw37827step0Labels = raw37827Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37827 raw37827Labels permutation8 permutation3
    _ = mixedMoment B node31 node31Labels := by rfl

def raw37828 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37828Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37828step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37828 raw37828Labels = mixedMoment B node23 node23Labels := by
  calc
    mixedMoment B raw37828 raw37828Labels = mixedMoment B raw37828step0 raw37828step0Labels := by
      have ha : raw37828step0 = (fun i j => raw37828 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37828step0 raw37828; decide +kernel
      have hl : raw37828step0Labels = raw37828Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37828 raw37828Labels permutation40 permutation3
    _ = mixedMoment B node23 node23Labels := by rfl

def raw37829 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw37829Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw37829step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37829 raw37829Labels = mixedMoment B node28 node28Labels := by
  calc
    mixedMoment B raw37829 raw37829Labels = mixedMoment B raw37829step0 raw37829step0Labels := by
      have ha : raw37829step0 = (fun i j => raw37829 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37829step0 raw37829; decide +kernel
      have hl : raw37829step0Labels = raw37829Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37829 raw37829Labels permutation10 permutation3
    _ = mixedMoment B node28 node28Labels := by rfl

def raw37830 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37830Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37830step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37830step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37830 raw37830Labels = mixedMoment B node33 node33Labels := by
  calc
    mixedMoment B raw37830 raw37830Labels = mixedMoment B raw37830step0 raw37830step0Labels := by
      have ha : raw37830step0 = (fun i j => raw37830 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37830step0 raw37830; decide +kernel
      have hl : raw37830step0Labels = raw37830Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37830 raw37830Labels permutation9 permutation3
    _ = mixedMoment B node33 node33Labels := by rfl

def raw37831 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37831Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37831step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37831step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37831 raw37831Labels = mixedMoment B node34 node34Labels := by
  calc
    mixedMoment B raw37831 raw37831Labels = mixedMoment B raw37831step0 raw37831step0Labels := by
      have ha : raw37831step0 = (fun i j => raw37831 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37831step0 raw37831; decide +kernel
      have hl : raw37831step0Labels = raw37831Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37831 raw37831Labels permutation8 permutation3
    _ = mixedMoment B node34 node34Labels := by rfl

def raw37832 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw37832Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37832step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw37832step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37832 raw37832Labels = mixedMoment B node35 node35Labels := by
  calc
    mixedMoment B raw37832 raw37832Labels = mixedMoment B raw37832step0 raw37832step0Labels := by
      have ha : raw37832step0 = (fun i j => raw37832 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37832step0 raw37832; decide +kernel
      have hl : raw37832step0Labels = raw37832Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37832 raw37832Labels permutation2 permutation3
    _ = mixedMoment B node35 node35Labels := by rfl

def raw37833 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37833Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37833step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw37833step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37833 raw37833Labels = mixedMoment B node25 node25Labels := by
  calc
    mixedMoment B raw37833 raw37833Labels = mixedMoment B raw37833step0 raw37833step0Labels := by
      have ha : raw37833step0 = (fun i j => raw37833 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37833step0 raw37833; decide +kernel
      have hl : raw37833step0Labels = raw37833Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37833 raw37833Labels permutation8 permutation3
    _ = mixedMoment B node25 node25Labels := by rfl

def raw37834 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw37834Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37834step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw37834step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37834 raw37834Labels = mixedMoment B node38 node38Labels := by
  calc
    mixedMoment B raw37834 raw37834Labels = mixedMoment B raw37834step0 raw37834step0Labels := by
      have ha : raw37834step0 = (fun i j => raw37834 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37834step0 raw37834; decide +kernel
      have hl : raw37834step0Labels = raw37834Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37834 raw37834Labels permutation2 permutation3
    _ = mixedMoment B node38 node38Labels := by rfl

def raw37835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37835Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37835step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37835 raw37835Labels = mixedMoment B node125 node125Labels := by
  calc
    mixedMoment B raw37835 raw37835Labels = mixedMoment B raw37835step0 raw37835step0Labels := by
      have ha : raw37835step0 = (fun i j => raw37835 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37835step0 raw37835; decide +kernel
      have hl : raw37835step0Labels = raw37835Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37835 raw37835Labels permutation152 permutation3
    _ = mixedMoment B node125 node125Labels := by rfl

def raw37836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37836Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37836step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37836 raw37836Labels = mixedMoment B node120 node120Labels := by
  calc
    mixedMoment B raw37836 raw37836Labels = mixedMoment B raw37836step0 raw37836step0Labels := by
      have ha : raw37836step0 = (fun i j => raw37836 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37836step0 raw37836; decide +kernel
      have hl : raw37836step0Labels = raw37836Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37836 raw37836Labels permutation164 permutation3
    _ = mixedMoment B node120 node120Labels := by rfl

def raw37837 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37837Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37837step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37837 raw37837Labels = mixedMoment B node126 node126Labels := by
  calc
    mixedMoment B raw37837 raw37837Labels = mixedMoment B raw37837step0 raw37837step0Labels := by
      have ha : raw37837step0 = (fun i j => raw37837 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37837step0 raw37837; decide +kernel
      have hl : raw37837step0Labels = raw37837Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37837 raw37837Labels permutation32 permutation3
    _ = mixedMoment B node126 node126Labels := by rfl

def raw37838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37838Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37838step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37838 raw37838Labels = mixedMoment B node118 node118Labels := by
  calc
    mixedMoment B raw37838 raw37838Labels = mixedMoment B raw37838step0 raw37838step0Labels := by
      have ha : raw37838step0 = (fun i j => raw37838 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37838step0 raw37838; decide +kernel
      have hl : raw37838step0Labels = raw37838Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37838 raw37838Labels permutation160 permutation3
    _ = mixedMoment B node118 node118Labels := by rfl

def raw37839 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw37839Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw37839step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37839 raw37839Labels = mixedMoment B node121 node121Labels := by
  calc
    mixedMoment B raw37839 raw37839Labels = mixedMoment B raw37839step0 raw37839step0Labels := by
      have ha : raw37839step0 = (fun i j => raw37839 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37839step0 raw37839; decide +kernel
      have hl : raw37839step0Labels = raw37839Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37839 raw37839Labels permutation34 permutation3
    _ = mixedMoment B node121 node121Labels := by rfl

def raw37840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37840Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37840step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37840 raw37840Labels = mixedMoment B node127 node127Labels := by
  calc
    mixedMoment B raw37840 raw37840Labels = mixedMoment B raw37840step0 raw37840step0Labels := by
      have ha : raw37840step0 = (fun i j => raw37840 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37840step0 raw37840; decide +kernel
      have hl : raw37840step0Labels = raw37840Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37840 raw37840Labels permutation33 permutation3
    _ = mixedMoment B node127 node127Labels := by rfl

def raw37841 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37841Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37841step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37841 raw37841Labels = mixedMoment B node128 node128Labels := by
  calc
    mixedMoment B raw37841 raw37841Labels = mixedMoment B raw37841step0 raw37841step0Labels := by
      have ha : raw37841step0 = (fun i j => raw37841 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37841step0 raw37841; decide +kernel
      have hl : raw37841step0Labels = raw37841Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37841 raw37841Labels permutation32 permutation3
    _ = mixedMoment B node128 node128Labels := by rfl

def raw37842 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw37842Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37842step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw37842step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37842 raw37842Labels = mixedMoment B node129 node129Labels := by
  calc
    mixedMoment B raw37842 raw37842Labels = mixedMoment B raw37842step0 raw37842step0Labels := by
      have ha : raw37842step0 = (fun i j => raw37842 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37842step0 raw37842; decide +kernel
      have hl : raw37842step0Labels = raw37842Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37842 raw37842Labels permutation8 permutation3
    _ = mixedMoment B node129 node129Labels := by rfl

def raw37843 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37843Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw37843step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37843 raw37843Labels = mixedMoment B node119 node119Labels := by
  calc
    mixedMoment B raw37843 raw37843Labels = mixedMoment B raw37843step0 raw37843step0Labels := by
      have ha : raw37843step0 = (fun i j => raw37843 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37843step0 raw37843; decide +kernel
      have hl : raw37843step0Labels = raw37843Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37843 raw37843Labels permutation32 permutation3
    _ = mixedMoment B node119 node119Labels := by rfl

def raw37844 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37844Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37844step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37844 raw37844Labels = mixedMoment B node124 node124Labels := by
  calc
    mixedMoment B raw37844 raw37844Labels = mixedMoment B raw37844step0 raw37844step0Labels := by
      have ha : raw37844step0 = (fun i j => raw37844 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37844step0 raw37844; decide +kernel
      have hl : raw37844step0Labels = raw37844Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37844 raw37844Labels permutation33 permutation3
    _ = mixedMoment B node124 node124Labels := by rfl

def raw37845 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw37845Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37845step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw37845step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37845step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw37845step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37845 raw37845Labels = mixedMoment B node70 node70Labels := by
  calc
    mixedMoment B raw37845 raw37845Labels = mixedMoment B raw37845step0 raw37845step0Labels := by
      have ha : raw37845step0 = (fun i j => raw37845 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37845step0 raw37845; decide +kernel
      have hl : raw37845step0Labels = raw37845Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37845 raw37845Labels permutation31 permutation3
    mixedMoment B raw37845step0 raw37845step0Labels = mixedMoment B raw37845step1 raw37845step1Labels := by
      have ha : raw37845step1 = -raw37845step0 := by apply Matrix.ext; change ∀ i j, raw37845step1 i j = -(raw37845step0 i j); unfold raw37845step1 raw37845step0; decide +kernel
      have hl : raw37845step1Labels = raw37845step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node70 node70Labels := by rfl

def raw37846 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw37846Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37846step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw37846step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37846 raw37846Labels = mixedMoment B node133 node133Labels := by
  calc
    mixedMoment B raw37846 raw37846Labels = mixedMoment B raw37846step0 raw37846step0Labels := by
      have ha : raw37846step0 = (fun i j => raw37846 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37846step0 raw37846; decide +kernel
      have hl : raw37846step0Labels = raw37846Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37846 raw37846Labels permutation8 permutation3
    _ = mixedMoment B node133 node133Labels := by rfl

def raw37847 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw37847Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37847step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw37847step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37847 raw37847Labels = mixedMoment B node132 node132Labels := by
  calc
    mixedMoment B raw37847 raw37847Labels = mixedMoment B raw37847step0 raw37847step0Labels := by
      have ha : raw37847step0 = (fun i j => raw37847 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37847step0 raw37847; decide +kernel
      have hl : raw37847step0Labels = raw37847Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37847 raw37847Labels permutation8 permutation3
    _ = mixedMoment B node132 node132Labels := by rfl

def raw37848 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw37848Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37848step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw37848step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37848 raw37848Labels = mixedMoment B node131 node131Labels := by
  calc
    mixedMoment B raw37848 raw37848Labels = mixedMoment B raw37848step0 raw37848step0Labels := by
      have ha : raw37848step0 = (fun i j => raw37848 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37848step0 raw37848; decide +kernel
      have hl : raw37848step0Labels = raw37848Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37848 raw37848Labels permutation8 permutation3
    _ = mixedMoment B node131 node131Labels := by rfl

def raw37849 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw37849Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw37849step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37849 raw37849Labels = mixedMoment B node137 node137Labels := by
  calc
    mixedMoment B raw37849 raw37849Labels = mixedMoment B raw37849step0 raw37849step0Labels := by
      have ha : raw37849step0 = (fun i j => raw37849 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37849step0 raw37849; decide +kernel
      have hl : raw37849step0Labels = raw37849Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37849 raw37849Labels permutation32 permutation3
    _ = mixedMoment B node137 node137Labels := by rfl

def raw37850 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw37850Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw37850step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37850 raw37850Labels = mixedMoment B node138 node138Labels := by
  calc
    mixedMoment B raw37850 raw37850Labels = mixedMoment B raw37850step0 raw37850step0Labels := by
      have ha : raw37850step0 = (fun i j => raw37850 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37850step0 raw37850; decide +kernel
      have hl : raw37850step0Labels = raw37850Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37850 raw37850Labels permutation32 permutation3
    _ = mixedMoment B node138 node138Labels := by rfl

def raw37851 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw37851Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37851step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw37851step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw37851step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37851 raw37851Labels = mixedMoment B node49 node49Labels := by
  calc
    mixedMoment B raw37851 raw37851Labels = mixedMoment B raw37851step0 raw37851step0Labels := by
      have ha : raw37851step0 = (fun i j => raw37851 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37851step0 raw37851; decide +kernel
      have hl : raw37851step0Labels = raw37851Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37851 raw37851Labels permutation29 permutation3
    mixedMoment B raw37851step0 raw37851step0Labels = mixedMoment B raw37851step1 raw37851step1Labels := by
      have ha : raw37851step1 = -raw37851step0 := by apply Matrix.ext; change ∀ i j, raw37851step1 i j = -(raw37851step0 i j); unfold raw37851step1 raw37851step0; decide +kernel
      have hl : raw37851step1Labels = raw37851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node49 node49Labels := by rfl

def raw37852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37852Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37852step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37852 raw37852Labels = mixedMoment B node141 node141Labels := by
  calc
    mixedMoment B raw37852 raw37852Labels = mixedMoment B raw37852step0 raw37852step0Labels := by
      have ha : raw37852step0 = (fun i j => raw37852 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37852step0 raw37852; decide +kernel
      have hl : raw37852step0Labels = raw37852Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37852 raw37852Labels permutation170 permutation3
    _ = mixedMoment B node141 node141Labels := by rfl

def raw37853 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw37853Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37853step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37853 raw37853Labels = mixedMoment B node144 node144Labels := by
  calc
    mixedMoment B raw37853 raw37853Labels = mixedMoment B raw37853step0 raw37853step0Labels := by
      have ha : raw37853step0 = (fun i j => raw37853 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37853step0 raw37853; decide +kernel
      have hl : raw37853step0Labels = raw37853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37853 raw37853Labels permutation32 permutation3
    _ = mixedMoment B node144 node144Labels := by rfl

def raw37854 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw37854Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37854step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37854 raw37854Labels = mixedMoment B node142 node142Labels := by
  calc
    mixedMoment B raw37854 raw37854Labels = mixedMoment B raw37854step0 raw37854step0Labels := by
      have ha : raw37854step0 = (fun i j => raw37854 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37854step0 raw37854; decide +kernel
      have hl : raw37854step0Labels = raw37854Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37854 raw37854Labels permutation34 permutation3
    _ = mixedMoment B node142 node142Labels := by rfl

def raw37855 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw37855Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37855step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw37855step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37855 raw37855Labels = mixedMoment B node146 node146Labels := by
  calc
    mixedMoment B raw37855 raw37855Labels = mixedMoment B raw37855step0 raw37855step0Labels := by
      have ha : raw37855step0 = (fun i j => raw37855 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37855step0 raw37855; decide +kernel
      have hl : raw37855step0Labels = raw37855Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37855 raw37855Labels permutation8 permutation3
    _ = mixedMoment B node146 node146Labels := by rfl

def raw37856 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37856Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37856step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw37856step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37856 raw37856Labels = mixedMoment B node143 node143Labels := by
  calc
    mixedMoment B raw37856 raw37856Labels = mixedMoment B raw37856step0 raw37856step0Labels := by
      have ha : raw37856step0 = (fun i j => raw37856 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37856step0 raw37856; decide +kernel
      have hl : raw37856step0Labels = raw37856Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37856 raw37856Labels permutation8 permutation3
    _ = mixedMoment B node143 node143Labels := by rfl

def raw37857 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37857Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37857step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw37857step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37857 raw37857Labels = mixedMoment B node149 node149Labels := by
  calc
    mixedMoment B raw37857 raw37857Labels = mixedMoment B raw37857step0 raw37857step0Labels := by
      have ha : raw37857step0 = (fun i j => raw37857 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37857step0 raw37857; decide +kernel
      have hl : raw37857step0Labels = raw37857Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37857 raw37857Labels permutation9 permutation3
    _ = mixedMoment B node149 node149Labels := by rfl

def raw37858 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw37858Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37858step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw37858step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37858step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw37858step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37858 raw37858Labels = mixedMoment B node100 node100Labels := by
  calc
    mixedMoment B raw37858 raw37858Labels = mixedMoment B raw37858step0 raw37858step0Labels := by
      have ha : raw37858step0 = (fun i j => raw37858 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37858step0 raw37858; decide +kernel
      have hl : raw37858step0Labels = raw37858Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37858 raw37858Labels permutation7 permutation3
    mixedMoment B raw37858step0 raw37858step0Labels = mixedMoment B raw37858step1 raw37858step1Labels := by
      have ha : raw37858step1 = -raw37858step0 := by apply Matrix.ext; change ∀ i j, raw37858step1 i j = -(raw37858step0 i j); unfold raw37858step1 raw37858step0; decide +kernel
      have hl : raw37858step1Labels = raw37858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node100 node100Labels := by rfl

def raw37859 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw37859Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37859step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw37859step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37859 raw37859Labels = mixedMoment B node135 node135Labels := by
  calc
    mixedMoment B raw37859 raw37859Labels = mixedMoment B raw37859step0 raw37859step0Labels := by
      have ha : raw37859step0 = (fun i j => raw37859 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37859step0 raw37859; decide +kernel
      have hl : raw37859step0Labels = raw37859Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37859 raw37859Labels permutation8 permutation3
    _ = mixedMoment B node135 node135Labels := by rfl

def raw37860 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw37860Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37860step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw37860step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37860 raw37860Labels = mixedMoment B node136 node136Labels := by
  calc
    mixedMoment B raw37860 raw37860Labels = mixedMoment B raw37860step0 raw37860step0Labels := by
      have ha : raw37860step0 = (fun i j => raw37860 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37860step0 raw37860; decide +kernel
      have hl : raw37860step0Labels = raw37860Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37860 raw37860Labels permutation8 permutation3
    _ = mixedMoment B node136 node136Labels := by rfl

def raw37861 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw37861Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37861step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw37861step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37861step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw37861step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37861 raw37861Labels = mixedMoment B node57 node57Labels := by
  calc
    mixedMoment B raw37861 raw37861Labels = mixedMoment B raw37861step0 raw37861step0Labels := by
      have ha : raw37861step0 = (fun i j => raw37861 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37861step0 raw37861; decide +kernel
      have hl : raw37861step0Labels = raw37861Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37861 raw37861Labels permutation7 permutation3
    mixedMoment B raw37861step0 raw37861step0Labels = mixedMoment B raw37861step1 raw37861step1Labels := by
      have ha : raw37861step1 = -raw37861step0 := by apply Matrix.ext; change ∀ i j, raw37861step1 i j = -(raw37861step0 i j); unfold raw37861step1 raw37861step0; decide +kernel
      have hl : raw37861step1Labels = raw37861step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node57 node57Labels := by rfl

def raw37862 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37862Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37862step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37862 raw37862Labels = mixedMoment B node151 node151Labels := by
  calc
    mixedMoment B raw37862 raw37862Labels = mixedMoment B raw37862step0 raw37862step0Labels := by
      have ha : raw37862step0 = (fun i j => raw37862 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37862step0 raw37862; decide +kernel
      have hl : raw37862step0Labels = raw37862Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37862 raw37862Labels permutation50 permutation3
    _ = mixedMoment B node151 node151Labels := by rfl

def raw37863 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37863Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37863 raw37863Labels = mixedMoment B node155 node155Labels := by
  calc
    _ = mixedMoment B node155 node155Labels := by rfl

def raw37864 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37864Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37864 raw37864Labels = mixedMoment B node156 node156Labels := by
  calc
    _ = mixedMoment B node156 node156Labels := by rfl

def raw37865 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37865Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37865 raw37865Labels = mixedMoment B node157 node157Labels := by
  calc
    _ = mixedMoment B node157 node157Labels := by rfl

def raw37866 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37866Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37866step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37866step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37866 raw37866Labels = mixedMoment B node152 node152Labels := by
  calc
    mixedMoment B raw37866 raw37866Labels = mixedMoment B raw37866step0 raw37866step0Labels := by
      have ha : raw37866step0 = (fun i j => raw37866 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37866step0 raw37866; decide +kernel
      have hl : raw37866step0Labels = raw37866Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37866 raw37866Labels permutation10 permutation3
    _ = mixedMoment B node152 node152Labels := by rfl

def raw37867 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw37867Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37867 raw37867Labels = mixedMoment B node158 node158Labels := by
  calc
    _ = mixedMoment B node158 node158Labels := by rfl

def raw37868 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37868Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37868step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37868step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37868 raw37868Labels = mixedMoment B node156 node156Labels := by
  calc
    mixedMoment B raw37868 raw37868Labels = mixedMoment B raw37868step0 raw37868step0Labels := by
      have ha : raw37868step0 = (fun i j => raw37868 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37868step0 raw37868; decide +kernel
      have hl : raw37868step0Labels = raw37868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37868 raw37868Labels permutation8 permutation3
    _ = mixedMoment B node156 node156Labels := by rfl

def raw37869 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw37869Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37869step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw37869step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37869 raw37869Labels = mixedMoment B node158 node158Labels := by
  calc
    mixedMoment B raw37869 raw37869Labels = mixedMoment B raw37869step0 raw37869step0Labels := by
      have ha : raw37869step0 = (fun i j => raw37869 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37869step0 raw37869; decide +kernel
      have hl : raw37869step0Labels = raw37869Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37869 raw37869Labels permutation2 permutation3
    _ = mixedMoment B node158 node158Labels := by rfl

def raw37870 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw37870Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37870step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw37870step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37870 raw37870Labels = mixedMoment B node154 node154Labels := by
  calc
    mixedMoment B raw37870 raw37870Labels = mixedMoment B raw37870step0 raw37870step0Labels := by
      have ha : raw37870step0 = (fun i j => raw37870 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37870step0 raw37870; decide +kernel
      have hl : raw37870step0Labels = raw37870Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37870 raw37870Labels permutation2 permutation3
    _ = mixedMoment B node154 node154Labels := by rfl

def raw37871 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw37871Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37871 raw37871Labels = mixedMoment B node160 node160Labels := by
  calc
    _ = mixedMoment B node160 node160Labels := by rfl

def raw37872 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw37872Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37872 raw37872Labels = mixedMoment B node161 node161Labels := by
  calc
    _ = mixedMoment B node161 node161Labels := by rfl

def raw37873 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw37873Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37873 raw37873Labels = mixedMoment B node162 node162Labels := by
  calc
    _ = mixedMoment B node162 node162Labels := by rfl

def raw37874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37874Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37874step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37874 raw37874Labels = mixedMoment B node63 node63Labels := by
  calc
    mixedMoment B raw37874 raw37874Labels = mixedMoment B raw37874step0 raw37874step0Labels := by
      have ha : raw37874step0 = (fun i j => raw37874 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37874step0 raw37874; decide +kernel
      have hl : raw37874step0Labels = raw37874Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37874 raw37874Labels permutation164 permutation3
    _ = mixedMoment B node63 node63Labels := by rfl

def raw37875 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37875Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37875step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37875 raw37875Labels = mixedMoment B node66 node66Labels := by
  calc
    mixedMoment B raw37875 raw37875Labels = mixedMoment B raw37875step0 raw37875step0Labels := by
      have ha : raw37875step0 = (fun i j => raw37875 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37875step0 raw37875; decide +kernel
      have hl : raw37875step0Labels = raw37875Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37875 raw37875Labels permutation32 permutation3
    _ = mixedMoment B node66 node66Labels := by rfl

def raw37876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37876Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37876step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37876 raw37876Labels = mixedMoment B node61 node61Labels := by
  calc
    mixedMoment B raw37876 raw37876Labels = mixedMoment B raw37876step0 raw37876step0Labels := by
      have ha : raw37876step0 = (fun i j => raw37876 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37876step0 raw37876; decide +kernel
      have hl : raw37876step0Labels = raw37876Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37876 raw37876Labels permutation160 permutation3
    _ = mixedMoment B node61 node61Labels := by rfl

def raw37877 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw37877Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw37877step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37877 raw37877Labels = mixedMoment B node64 node64Labels := by
  calc
    mixedMoment B raw37877 raw37877Labels = mixedMoment B raw37877step0 raw37877step0Labels := by
      have ha : raw37877step0 = (fun i j => raw37877 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37877step0 raw37877; decide +kernel
      have hl : raw37877step0Labels = raw37877Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37877 raw37877Labels permutation34 permutation3
    _ = mixedMoment B node64 node64Labels := by rfl

def raw37878 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37878Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37878step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37878 raw37878Labels = mixedMoment B node68 node68Labels := by
  calc
    mixedMoment B raw37878 raw37878Labels = mixedMoment B raw37878step0 raw37878step0Labels := by
      have ha : raw37878step0 = (fun i j => raw37878 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37878step0 raw37878; decide +kernel
      have hl : raw37878step0Labels = raw37878Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37878 raw37878Labels permutation33 permutation3
    _ = mixedMoment B node68 node68Labels := by rfl

def raw37879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37879Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37879step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37879 raw37879Labels = mixedMoment B node69 node69Labels := by
  calc
    mixedMoment B raw37879 raw37879Labels = mixedMoment B raw37879step0 raw37879step0Labels := by
      have ha : raw37879step0 = (fun i j => raw37879 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37879step0 raw37879; decide +kernel
      have hl : raw37879step0Labels = raw37879Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37879 raw37879Labels permutation32 permutation3
    _ = mixedMoment B node69 node69Labels := by rfl

def raw37880 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37880Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw37880step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37880 raw37880Labels = mixedMoment B node62 node62Labels := by
  calc
    mixedMoment B raw37880 raw37880Labels = mixedMoment B raw37880step0 raw37880step0Labels := by
      have ha : raw37880step0 = (fun i j => raw37880 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37880step0 raw37880; decide +kernel
      have hl : raw37880step0Labels = raw37880Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37880 raw37880Labels permutation32 permutation3
    _ = mixedMoment B node62 node62Labels := by rfl

def raw37881 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw37881Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37881step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw37881step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37881 raw37881Labels = mixedMoment B node71 node71Labels := by
  calc
    mixedMoment B raw37881 raw37881Labels = mixedMoment B raw37881step0 raw37881step0Labels := by
      have ha : raw37881step0 = (fun i j => raw37881 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37881step0 raw37881; decide +kernel
      have hl : raw37881step0Labels = raw37881Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37881 raw37881Labels permutation8 permutation3
    _ = mixedMoment B node71 node71Labels := by rfl

def raw37882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw37882Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37882step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37882 raw37882Labels = mixedMoment B node79 node79Labels := by
  calc
    mixedMoment B raw37882 raw37882Labels = mixedMoment B raw37882step0 raw37882step0Labels := by
      have ha : raw37882step0 = (fun i j => raw37882 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37882step0 raw37882; decide +kernel
      have hl : raw37882step0Labels = raw37882Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37882 raw37882Labels permutation176 permutation3
    _ = mixedMoment B node79 node79Labels := by rfl

def raw37883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw37883Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37883step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37883 raw37883Labels = mixedMoment B node77 node77Labels := by
  calc
    mixedMoment B raw37883 raw37883Labels = mixedMoment B raw37883step0 raw37883step0Labels := by
      have ha : raw37883step0 = (fun i j => raw37883 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37883step0 raw37883; decide +kernel
      have hl : raw37883step0Labels = raw37883Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37883 raw37883Labels permutation178 permutation3
    _ = mixedMoment B node77 node77Labels := by rfl

def raw37884 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw37884Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw37884step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37884 raw37884Labels = mixedMoment B node80 node80Labels := by
  calc
    mixedMoment B raw37884 raw37884Labels = mixedMoment B raw37884step0 raw37884step0Labels := by
      have ha : raw37884step0 = (fun i j => raw37884 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37884step0 raw37884; decide +kernel
      have hl : raw37884step0Labels = raw37884Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37884 raw37884Labels permutation38 permutation3
    _ = mixedMoment B node80 node80Labels := by rfl

def raw37885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37885Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw37885step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37885 raw37885Labels = mixedMoment B node78 node78Labels := by
  calc
    mixedMoment B raw37885 raw37885Labels = mixedMoment B raw37885step0 raw37885step0Labels := by
      have ha : raw37885step0 = (fun i j => raw37885 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37885step0 raw37885; decide +kernel
      have hl : raw37885step0Labels = raw37885Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37885 raw37885Labels permutation38 permutation3
    _ = mixedMoment B node78 node78Labels := by rfl

def raw37886 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37886Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw37886step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37886 raw37886Labels = mixedMoment B node81 node81Labels := by
  calc
    mixedMoment B raw37886 raw37886Labels = mixedMoment B raw37886step0 raw37886step0Labels := by
      have ha : raw37886step0 = (fun i j => raw37886 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37886step0 raw37886; decide +kernel
      have hl : raw37886step0Labels = raw37886Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37886 raw37886Labels permutation39 permutation3
    _ = mixedMoment B node81 node81Labels := by rfl

def raw37887 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw37887Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37887step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw37887step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37887 raw37887Labels = mixedMoment B node82 node82Labels := by
  calc
    mixedMoment B raw37887 raw37887Labels = mixedMoment B raw37887step0 raw37887step0Labels := by
      have ha : raw37887step0 = (fun i j => raw37887 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37887step0 raw37887; decide +kernel
      have hl : raw37887step0Labels = raw37887Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37887 raw37887Labels permutation10 permutation3
    _ = mixedMoment B node82 node82Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
