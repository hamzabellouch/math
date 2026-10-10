import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32000 raw32000Labels = mixedMoment B node2849 node2849Labels := by
  calc
    mixedMoment B raw32000 raw32000Labels = mixedMoment B raw32000step0 raw32000step0Labels := by
      have ha : raw32000step0 = (fun i j => raw32000 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32000step0 raw32000; decide +kernel
      have hl : raw32000step0Labels = raw32000Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32000 raw32000Labels permutation176 permutation2
    _ = mixedMoment B node2849 node2849Labels := by rfl

def raw32001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32001 raw32001Labels = mixedMoment B node2847 node2847Labels := by
  calc
    mixedMoment B raw32001 raw32001Labels = mixedMoment B raw32001step0 raw32001step0Labels := by
      have ha : raw32001step0 = (fun i j => raw32001 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32001step0 raw32001; decide +kernel
      have hl : raw32001step0Labels = raw32001Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32001 raw32001Labels permutation176 permutation2
    _ = mixedMoment B node2847 node2847Labels := by rfl

def raw32002 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32002 raw32002Labels = mixedMoment B node3384 node3384Labels := by
  calc
    mixedMoment B raw32002 raw32002Labels = mixedMoment B raw32002step0 raw32002step0Labels := by
      have ha : raw32002step0 = (fun i j => raw32002 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32002step0 raw32002; decide +kernel
      have hl : raw32002step0Labels = raw32002Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32002 raw32002Labels permutation176 permutation2
    mixedMoment B raw32002step0 raw32002step0Labels = mixedMoment B raw32002step1 raw32002step1Labels := by
      have ha : raw32002step1 = -raw32002step0 := by apply Matrix.ext; change ∀ i j, raw32002step1 i j = -(raw32002step0 i j); unfold raw32002step1 raw32002step0; decide +kernel
      have hl : raw32002step1Labels = raw32002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3384 node3384Labels := by rfl

def raw32003 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32003 raw32003Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw32003 raw32003Labels = mixedMoment B raw32003step0 raw32003step0Labels := by
      have ha : raw32003step0 = (fun i j => raw32003 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32003step0 raw32003; decide +kernel
      have hl : raw32003step0Labels = raw32003Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32003 raw32003Labels permutation176 permutation2
    mixedMoment B raw32003step0 raw32003step0Labels = mixedMoment B raw32003step1 raw32003step1Labels := by
      have ha : raw32003step1 = -raw32003step0 := by apply Matrix.ext; change ∀ i j, raw32003step1 i j = -(raw32003step0 i j); unfold raw32003step1 raw32003step0; decide +kernel
      have hl : raw32003step1Labels = raw32003step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw32004 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32004 raw32004Labels = mixedMoment B node3371 node3371Labels := by
  calc
    mixedMoment B raw32004 raw32004Labels = mixedMoment B raw32004step0 raw32004step0Labels := by
      have ha : raw32004step0 = (fun i j => raw32004 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32004step0 raw32004; decide +kernel
      have hl : raw32004step0Labels = raw32004Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32004 raw32004Labels permutation179 permutation2
    mixedMoment B raw32004step0 raw32004step0Labels = mixedMoment B raw32004step1 raw32004step1Labels := by
      have ha : raw32004step1 = -raw32004step0 := by apply Matrix.ext; change ∀ i j, raw32004step1 i j = -(raw32004step0 i j); unfold raw32004step1 raw32004step0; decide +kernel
      have hl : raw32004step1Labels = raw32004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3371 node3371Labels := by rfl

def raw32005 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32005 raw32005Labels = mixedMoment B node3371 node3371Labels := by
  calc
    mixedMoment B raw32005 raw32005Labels = mixedMoment B raw32005step0 raw32005step0Labels := by
      have ha : raw32005step0 = (fun i j => raw32005 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32005step0 raw32005; decide +kernel
      have hl : raw32005step0Labels = raw32005Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32005 raw32005Labels permutation177 permutation2
    mixedMoment B raw32005step0 raw32005step0Labels = mixedMoment B raw32005step1 raw32005step1Labels := by
      have ha : raw32005step1 = -raw32005step0 := by apply Matrix.ext; change ∀ i j, raw32005step1 i j = -(raw32005step0 i j); unfold raw32005step1 raw32005step0; decide +kernel
      have hl : raw32005step1Labels = raw32005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3371 node3371Labels := by rfl

def raw32006 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32006 raw32006Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw32006 raw32006Labels = mixedMoment B raw32006step0 raw32006step0Labels := by
      have ha : raw32006step0 = (fun i j => raw32006 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32006step0 raw32006; decide +kernel
      have hl : raw32006step0Labels = raw32006Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32006 raw32006Labels permutation176 permutation2
    mixedMoment B raw32006step0 raw32006step0Labels = mixedMoment B raw32006step1 raw32006step1Labels := by
      have ha : raw32006step1 = -raw32006step0 := by apply Matrix.ext; change ∀ i j, raw32006step1 i j = -(raw32006step0 i j); unfold raw32006step1 raw32006step0; decide +kernel
      have hl : raw32006step1Labels = raw32006step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3370 node3370Labels := by rfl

def raw32007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw32007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32007 raw32007Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw32007 raw32007Labels = mixedMoment B raw32007step0 raw32007step0Labels := by
      have ha : raw32007step0 = (fun i j => raw32007 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32007step0 raw32007; decide +kernel
      have hl : raw32007step0Labels = raw32007Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32007 raw32007Labels permutation662 permutation2
    mixedMoment B raw32007step0 raw32007step0Labels = mixedMoment B raw32007step1 raw32007step1Labels := by
      have ha : raw32007step1 = -raw32007step0 := by apply Matrix.ext; change ∀ i j, raw32007step1 i j = -(raw32007step0 i j); unfold raw32007step1 raw32007step0; decide +kernel
      have hl : raw32007step1Labels = raw32007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3781 node3781Labels := by rfl

def raw32008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32008 raw32008Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw32008 raw32008Labels = mixedMoment B raw32008step0 raw32008step0Labels := by
      have ha : raw32008step0 = (fun i j => raw32008 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32008step0 raw32008; decide +kernel
      have hl : raw32008step0Labels = raw32008Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32008 raw32008Labels permutation154 permutation2
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw32009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32009 raw32009Labels = mixedMoment B node2846 node2846Labels := by
  calc
    mixedMoment B raw32009 raw32009Labels = mixedMoment B raw32009step0 raw32009step0Labels := by
      have ha : raw32009step0 = (fun i j => raw32009 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32009step0 raw32009; decide +kernel
      have hl : raw32009step0Labels = raw32009Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32009 raw32009Labels permutation178 permutation2
    _ = mixedMoment B node2846 node2846Labels := by rfl

def raw32010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32010 raw32010Labels = mixedMoment B node2848 node2848Labels := by
  calc
    mixedMoment B raw32010 raw32010Labels = mixedMoment B raw32010step0 raw32010step0Labels := by
      have ha : raw32010step0 = (fun i j => raw32010 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32010step0 raw32010; decide +kernel
      have hl : raw32010step0Labels = raw32010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32010 raw32010Labels permutation176 permutation2
    _ = mixedMoment B node2848 node2848Labels := by rfl

def raw32011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw32011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32011 raw32011Labels = mixedMoment B node2426 node2426Labels := by
  calc
    mixedMoment B raw32011 raw32011Labels = mixedMoment B raw32011step0 raw32011step0Labels := by
      have ha : raw32011step0 = (fun i j => raw32011 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32011step0 raw32011; decide +kernel
      have hl : raw32011step0Labels = raw32011Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32011 raw32011Labels permutation662 permutation2
    mixedMoment B raw32011step0 raw32011step0Labels = mixedMoment B raw32011step1 raw32011step1Labels := by
      have ha : raw32011step1 = -raw32011step0 := by apply Matrix.ext; change ∀ i j, raw32011step1 i j = -(raw32011step0 i j); unfold raw32011step1 raw32011step0; decide +kernel
      have hl : raw32011step1Labels = raw32011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2426 node2426Labels := by rfl

def raw32012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw32012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32012 raw32012Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw32012 raw32012Labels = mixedMoment B raw32012step0 raw32012step0Labels := by
      have ha : raw32012step0 = (fun i j => raw32012 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32012step0 raw32012; decide +kernel
      have hl : raw32012step0Labels = raw32012Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32012 raw32012Labels permutation662 permutation2
    mixedMoment B raw32012step0 raw32012step0Labels = mixedMoment B raw32012step1 raw32012step1Labels := by
      have ha : raw32012step1 = -raw32012step0 := by apply Matrix.ext; change ∀ i j, raw32012step1 i j = -(raw32012step0 i j); unfold raw32012step1 raw32012step0; decide +kernel
      have hl : raw32012step1Labels = raw32012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3493 node3493Labels := by rfl

def raw32013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32013 raw32013Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw32013 raw32013Labels = mixedMoment B raw32013step0 raw32013step0Labels := by
      have hz : ∀ j, raw32013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32013step0 = (fun i j => raw32013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32013step0 raw32013; decide +kernel
      have hl : raw32013step0Labels = raw32013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32013 raw32013Labels permutation265 hz
    _ = mixedMoment B node2509 node2509Labels := by rfl

def raw32014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32014 raw32014Labels = mixedMoment B node2552 node2552Labels := by
  calc
    _ = mixedMoment B node2552 node2552Labels := by rfl

def raw32015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32015 raw32015Labels = mixedMoment B node2427 node2427Labels := by
  calc
    mixedMoment B raw32015 raw32015Labels = mixedMoment B raw32015step0 raw32015step0Labels := by
      have ha : raw32015step0 = (fun i j => raw32015 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32015step0 raw32015; decide +kernel
      have hl : raw32015step0Labels = raw32015Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32015 raw32015Labels permutation178 permutation2
    _ = mixedMoment B node2427 node2427Labels := by rfl

def raw32016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw32016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw32016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32016step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32016 raw32016Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw32016 raw32016Labels = mixedMoment B raw32016step0 raw32016step0Labels := by
      have ha : raw32016step0 = (fun i j => raw32016 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32016step0 raw32016; decide +kernel
      have hl : raw32016step0Labels = raw32016Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32016 raw32016Labels permutation662 permutation2
    mixedMoment B raw32016step0 raw32016step0Labels = mixedMoment B raw32016step1 raw32016step1Labels := by
      have ha : raw32016step1 = -raw32016step0 := by apply Matrix.ext; change ∀ i j, raw32016step1 i j = -(raw32016step0 i j); unfold raw32016step1 raw32016step0; decide +kernel
      have hl : raw32016step1Labels = raw32016step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1960 node1960Labels := by rfl

def raw32017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32017 raw32017Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw32017 raw32017Labels = mixedMoment B raw32017step0 raw32017step0Labels := by
      have ha : raw32017step0 = (fun i j => raw32017 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32017step0 raw32017; decide +kernel
      have hl : raw32017step0Labels = raw32017Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32017 raw32017Labels permutation176 permutation2
    _ = mixedMoment B node3781 node3781Labels := by rfl

def raw32018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32018 raw32018Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw32018 raw32018Labels = mixedMoment B raw32018step0 raw32018step0Labels := by
      have hz : ∀ j, raw32018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32018step0 = (fun i j => raw32018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32018step0 raw32018; decide +kernel
      have hl : raw32018step0Labels = raw32018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32018 raw32018Labels permutation265 hz
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw32019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32019 raw32019Labels = mixedMoment B node2554 node2554Labels := by
  calc
    _ = mixedMoment B node2554 node2554Labels := by rfl

def raw32020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32020 raw32020Labels = mixedMoment B node2433 node2433Labels := by
  calc
    mixedMoment B raw32020 raw32020Labels = mixedMoment B raw32020step0 raw32020step0Labels := by
      have ha : raw32020step0 = (fun i j => raw32020 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32020step0 raw32020; decide +kernel
      have hl : raw32020step0Labels = raw32020Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32020 raw32020Labels permutation178 permutation2
    _ = mixedMoment B node2433 node2433Labels := by rfl

def raw32021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw32021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32021 raw32021Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw32021 raw32021Labels = mixedMoment B raw32021step0 raw32021step0Labels := by
      have ha : raw32021step0 = (fun i j => raw32021 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32021step0 raw32021; decide +kernel
      have hl : raw32021step0Labels = raw32021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32021 raw32021Labels permutation177 permutation2
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw32022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32022 raw32022Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw32022 raw32022Labels = mixedMoment B raw32022step0 raw32022step0Labels := by
      have hz : ∀ j, raw32022 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32022step0 = (fun i j => raw32022 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32022step0 raw32022; decide +kernel
      have hl : raw32022step0Labels = raw32022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32022 raw32022Labels permutation265 hz
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw32023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32023 raw32023Labels = mixedMoment B node2433 node2433Labels := by
  calc
    mixedMoment B raw32023 raw32023Labels = mixedMoment B raw32023step0 raw32023step0Labels := by
      have ha : raw32023step0 = (fun i j => raw32023 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32023step0 raw32023; decide +kernel
      have hl : raw32023step0Labels = raw32023Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32023 raw32023Labels permutation179 permutation2
    _ = mixedMoment B node2433 node2433Labels := by rfl

def raw32024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw32024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32024 raw32024Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw32024 raw32024Labels = mixedMoment B raw32024step0 raw32024step0Labels := by
      have ha : raw32024step0 = (fun i j => raw32024 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32024step0 raw32024; decide +kernel
      have hl : raw32024step0Labels = raw32024Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32024 raw32024Labels permutation177 permutation2
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw32025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw32025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw32025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32025 raw32025Labels = mixedMoment B node2430 node2430Labels := by
  calc
    mixedMoment B raw32025 raw32025Labels = mixedMoment B raw32025step0 raw32025step0Labels := by
      have ha : raw32025step0 = (fun i j => raw32025 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32025step0 raw32025; decide +kernel
      have hl : raw32025step0Labels = raw32025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32025 raw32025Labels permutation176 permutation2
    _ = mixedMoment B node2430 node2430Labels := by rfl

def raw32026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw32026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32026 raw32026Labels = mixedMoment B node1335 node1335Labels := by
  calc
    mixedMoment B raw32026 raw32026Labels = mixedMoment B raw32026step0 raw32026step0Labels := by
      have ha : raw32026step0 = (fun i j => raw32026 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32026step0 raw32026; decide +kernel
      have hl : raw32026step0Labels = raw32026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32026 raw32026Labels permutation166 permutation2
    _ = mixedMoment B node1335 node1335Labels := by rfl

def raw32027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw32027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32027 raw32027Labels = mixedMoment B node2826 node2826Labels := by
  calc
    mixedMoment B raw32027 raw32027Labels = mixedMoment B raw32027step0 raw32027step0Labels := by
      have ha : raw32027step0 = (fun i j => raw32027 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32027step0 raw32027; decide +kernel
      have hl : raw32027step0Labels = raw32027Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32027 raw32027Labels permutation166 permutation2
    _ = mixedMoment B node2826 node2826Labels := by rfl

def raw32028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw32028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32028 raw32028Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw32028 raw32028Labels = mixedMoment B raw32028step0 raw32028step0Labels := by
      have ha : raw32028step0 = (fun i j => raw32028 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32028step0 raw32028; decide +kernel
      have hl : raw32028step0Labels = raw32028Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32028 raw32028Labels permutation154 permutation2
    _ = mixedMoment B node2933 node2933Labels := by rfl

def raw32029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw32029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32029 raw32029Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw32029 raw32029Labels = mixedMoment B raw32029step0 raw32029step0Labels := by
      have ha : raw32029step0 = (fun i j => raw32029 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32029step0 raw32029; decide +kernel
      have hl : raw32029step0Labels = raw32029Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32029 raw32029Labels permutation166 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw32030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw32030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32030 raw32030Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw32030 raw32030Labels = mixedMoment B raw32030step0 raw32030step0Labels := by
      have ha : raw32030step0 = (fun i j => raw32030 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32030step0 raw32030; decide +kernel
      have hl : raw32030step0Labels = raw32030Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32030 raw32030Labels permutation166 permutation2
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw32031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32031 raw32031Labels = mixedMoment B node4967 node4967Labels := by
  calc
    _ = mixedMoment B node4967 node4967Labels := by rfl

def raw32032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32032 raw32032Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw32032 raw32032Labels = mixedMoment B raw32032step0 raw32032step0Labels := by
      have hz : ∀ j, raw32032 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32032step0 = (fun i j => raw32032 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32032step0 raw32032; decide +kernel
      have hl : raw32032step0Labels = raw32032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32032 raw32032Labels permutation520 hz
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw32033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32033 raw32033Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw32033 raw32033Labels = mixedMoment B raw32033step0 raw32033step0Labels := by
      have hz : ∀ j, raw32033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32033step0 = (fun i j => raw32033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32033step0 raw32033; decide +kernel
      have hl : raw32033step0Labels = raw32033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32033 raw32033Labels permutation346 hz
    mixedMoment B raw32033step0 raw32033step0Labels = mixedMoment B raw32033step1 raw32033step1Labels := by
      have ha : raw32033step1 = (fun i j => raw32033step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32033step1 raw32033step0; decide +kernel
      have hl : raw32033step1Labels = raw32033step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32033step0 raw32033step0Labels permutation34 permutation2
    _ = mixedMoment B node4973 node4973Labels := by rfl

def raw32034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32034 raw32034Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw32034 raw32034Labels = mixedMoment B raw32034step0 raw32034step0Labels := by
      have ha : raw32034step0 = (fun i j => raw32034 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32034step0 raw32034; decide +kernel
      have hl : raw32034step0Labels = raw32034Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32034 raw32034Labels permutation154 permutation2
    _ = mixedMoment B node5114 node5114Labels := by rfl

def raw32035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32035 raw32035Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw32035 raw32035Labels = mixedMoment B raw32035step0 raw32035step0Labels := by
      have hz : ∀ j, raw32035 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32035step0 = (fun i j => raw32035 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32035step0 raw32035; decide +kernel
      have hl : raw32035step0Labels = raw32035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32035 raw32035Labels permutation520 hz
    mixedMoment B raw32035step0 raw32035step0Labels = mixedMoment B raw32035step1 raw32035step1Labels := by
      have hz : ∀ j, raw32035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32035step1 = (fun i j => raw32035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32035step1 raw32035step0; decide +kernel
      have hl : raw32035step1Labels = raw32035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32035step0 raw32035step0Labels permutation80 hz
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw32036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32036step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32036 raw32036Labels = mixedMoment B node3739 node3739Labels := by
  calc
    mixedMoment B raw32036 raw32036Labels = mixedMoment B raw32036step0 raw32036step0Labels := by
      have hz : ∀ j, raw32036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32036step0 = (fun i j => raw32036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32036step0 raw32036; decide +kernel
      have hl : raw32036step0Labels = raw32036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32036 raw32036Labels permutation346 hz
    mixedMoment B raw32036step0 raw32036step0Labels = mixedMoment B raw32036step1 raw32036step1Labels := by
      have ha : raw32036step1 = (fun i j => raw32036step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32036step1 raw32036step0; decide +kernel
      have hl : raw32036step1Labels = raw32036step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32036step0 raw32036step0Labels permutation56 permutation3
    _ = mixedMoment B node3739 node3739Labels := by rfl

def raw32037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32037 raw32037Labels = mixedMoment B node4031 node4031Labels := by
  calc
    mixedMoment B raw32037 raw32037Labels = mixedMoment B raw32037step0 raw32037step0Labels := by
      have ha : raw32037step0 = (fun i j => raw32037 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32037step0 raw32037; decide +kernel
      have hl : raw32037step0Labels = raw32037Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32037 raw32037Labels permutation152 permutation3
    _ = mixedMoment B node4031 node4031Labels := by rfl

def raw32038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32038step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32038step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw32038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32038 raw32038Labels = mixedMoment B node4037 node4037Labels := by
  calc
    mixedMoment B raw32038 raw32038Labels = mixedMoment B raw32038step0 raw32038step0Labels := by
      have hz : ∀ j, raw32038 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32038step0 = (fun i j => raw32038 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32038step0 raw32038; decide +kernel
      have hl : raw32038step0Labels = raw32038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32038 raw32038Labels permutation520 hz
    mixedMoment B raw32038step0 raw32038step0Labels = mixedMoment B raw32038step1 raw32038step1Labels := by
      have hz : ∀ j, raw32038step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32038step1 = (fun i j => raw32038step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32038step1 raw32038step0; decide +kernel
      have hl : raw32038step1Labels = raw32038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32038step0 raw32038step0Labels permutation80 hz
    mixedMoment B raw32038step1 raw32038step1Labels = mixedMoment B raw32038step2 raw32038step2Labels := by
      have ha : raw32038step2 = (fun i j => raw32038step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32038step2 raw32038step1; decide +kernel
      have hl : raw32038step2Labels = raw32038step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32038step1 raw32038step1Labels permutation8 permutation3
    _ = mixedMoment B node4037 node4037Labels := by rfl

def raw32039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32039 raw32039Labels = mixedMoment B node2814 node2814Labels := by
  calc
    mixedMoment B raw32039 raw32039Labels = mixedMoment B raw32039step0 raw32039step0Labels := by
      have ha : raw32039step0 = (fun i j => raw32039 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32039step0 raw32039; decide +kernel
      have hl : raw32039step0Labels = raw32039Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32039 raw32039Labels permutation152 permutation3
    _ = mixedMoment B node2814 node2814Labels := by rfl

def raw32040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32040step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32040 raw32040Labels = mixedMoment B node2963 node2963Labels := by
  calc
    mixedMoment B raw32040 raw32040Labels = mixedMoment B raw32040step0 raw32040step0Labels := by
      have hz : ∀ j, raw32040 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32040step0 = (fun i j => raw32040 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32040step0 raw32040; decide +kernel
      have hl : raw32040step0Labels = raw32040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32040 raw32040Labels permutation520 hz
    mixedMoment B raw32040step0 raw32040step0Labels = mixedMoment B raw32040step1 raw32040step1Labels := by
      have ha : raw32040step1 = (fun i j => raw32040step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32040step1 raw32040step0; decide +kernel
      have hl : raw32040step1Labels = raw32040step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32040step0 raw32040step0Labels permutation32 permutation3
    _ = mixedMoment B node2963 node2963Labels := by rfl

def raw32041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32041step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32041 raw32041Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw32041 raw32041Labels = mixedMoment B raw32041step0 raw32041step0Labels := by
      have hz : ∀ j, raw32041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32041step0 = (fun i j => raw32041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32041step0 raw32041; decide +kernel
      have hl : raw32041step0Labels = raw32041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32041 raw32041Labels permutation346 hz
    mixedMoment B raw32041step0 raw32041step0Labels = mixedMoment B raw32041step1 raw32041step1Labels := by
      have ha : raw32041step1 = (fun i j => raw32041step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32041step1 raw32041step0; decide +kernel
      have hl : raw32041step1Labels = raw32041step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32041step0 raw32041step0Labels permutation35 permutation3
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw32042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32042 raw32042Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw32042 raw32042Labels = mixedMoment B raw32042step0 raw32042step0Labels := by
      have ha : raw32042step0 = (fun i j => raw32042 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32042step0 raw32042; decide +kernel
      have hl : raw32042step0Labels = raw32042Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32042 raw32042Labels permutation155 permutation3
    _ = mixedMoment B node2896 node2896Labels := by rfl

def raw32043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32043step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32043step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw32043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32043 raw32043Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw32043 raw32043Labels = mixedMoment B raw32043step0 raw32043step0Labels := by
      have hz : ∀ j, raw32043 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32043step0 = (fun i j => raw32043 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32043step0 raw32043; decide +kernel
      have hl : raw32043step0Labels = raw32043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32043 raw32043Labels permutation520 hz
    mixedMoment B raw32043step0 raw32043step0Labels = mixedMoment B raw32043step1 raw32043step1Labels := by
      have hz : ∀ j, raw32043step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32043step1 = (fun i j => raw32043step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32043step1 raw32043step0; decide +kernel
      have hl : raw32043step1Labels = raw32043step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32043step0 raw32043step0Labels permutation80 hz
    mixedMoment B raw32043step1 raw32043step1Labels = mixedMoment B raw32043step2 raw32043step2Labels := by
      have ha : raw32043step2 = (fun i j => raw32043step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32043step2 raw32043step1; decide +kernel
      have hl : raw32043step2Labels = raw32043step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32043step1 raw32043step1Labels permutation9 permutation3
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw32044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32044 raw32044Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw32044 raw32044Labels = mixedMoment B raw32044step0 raw32044step0Labels := by
      have hz : ∀ j, raw32044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32044step0 = (fun i j => raw32044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32044step0 raw32044; decide +kernel
      have hl : raw32044step0Labels = raw32044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32044 raw32044Labels permutation346 hz
    mixedMoment B raw32044step0 raw32044step0Labels = mixedMoment B raw32044step1 raw32044step1Labels := by
      have ha : raw32044step1 = (fun i j => raw32044step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32044step1 raw32044step0; decide +kernel
      have hl : raw32044step1Labels = raw32044step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32044step0 raw32044step0Labels permutation36 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw32045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32045step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32045 raw32045Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw32045 raw32045Labels = mixedMoment B raw32045step0 raw32045step0Labels := by
      have ha : raw32045step0 = (fun i j => raw32045 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32045step0 raw32045; decide +kernel
      have hl : raw32045step0Labels = raw32045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32045 raw32045Labels permutation160 permutation3
    mixedMoment B raw32045step0 raw32045step0Labels = mixedMoment B raw32045step1 raw32045step1Labels := by
      have ha : raw32045step1 = raw32045step0 := by apply Matrix.ext; unfold raw32045step1 raw32045step0; decide +kernel
      have hl : raw32045step0Labels = labelEmbedding6 ∘ raw32045step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32045step0 raw32045step0Labels raw32045step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw32046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32046step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32046 raw32046Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw32046 raw32046Labels = mixedMoment B raw32046step0 raw32046step0Labels := by
      have ha : raw32046step0 = (fun i j => raw32046 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32046step0 raw32046; decide +kernel
      have hl : raw32046step0Labels = raw32046Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32046 raw32046Labels permutation166 permutation3
    mixedMoment B raw32046step0 raw32046step0Labels = mixedMoment B raw32046step1 raw32046step1Labels := by
      have ha : raw32046step1 = raw32046step0 := by apply Matrix.ext; unfold raw32046step1 raw32046step0; decide +kernel
      have hl : raw32046step0Labels = labelEmbedding6 ∘ raw32046step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32046step0 raw32046step0Labels raw32046step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw32047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32047step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32047 raw32047Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw32047 raw32047Labels = mixedMoment B raw32047step0 raw32047step0Labels := by
      have hz : ∀ j, raw32047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32047step0 = (fun i j => raw32047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32047step0 raw32047; decide +kernel
      have hl : raw32047step0Labels = raw32047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32047 raw32047Labels permutation346 hz
    mixedMoment B raw32047step0 raw32047step0Labels = mixedMoment B raw32047step1 raw32047step1Labels := by
      have ha : raw32047step1 = (fun i j => raw32047step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32047step1 raw32047step0; decide +kernel
      have hl : raw32047step1Labels = raw32047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32047step0 raw32047step0Labels permutation34 permutation3
    mixedMoment B raw32047step1 raw32047step1Labels = mixedMoment B raw32047step2 raw32047step2Labels := by
      have ha : raw32047step2 = raw32047step1 := by apply Matrix.ext; unfold raw32047step2 raw32047step1; decide +kernel
      have hl : raw32047step1Labels = labelEmbedding6 ∘ raw32047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32047step1 raw32047step1Labels raw32047step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw32048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32048 raw32048Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw32048 raw32048Labels = mixedMoment B raw32048step0 raw32048step0Labels := by
      have ha : raw32048step0 = (fun i j => raw32048 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32048step0 raw32048; decide +kernel
      have hl : raw32048step0Labels = raw32048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32048 raw32048Labels permutation178 permutation3
    mixedMoment B raw32048step0 raw32048step0Labels = mixedMoment B raw32048step1 raw32048step1Labels := by
      have ha : raw32048step1 = raw32048step0 := by apply Matrix.ext; unfold raw32048step1 raw32048step0; decide +kernel
      have hl : raw32048step0Labels = labelEmbedding6 ∘ raw32048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32048step0 raw32048step0Labels raw32048step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw32049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32049step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32049step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32049 raw32049Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw32049 raw32049Labels = mixedMoment B raw32049step0 raw32049step0Labels := by
      have hz : ∀ j, raw32049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32049step0 = (fun i j => raw32049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32049step0 raw32049; decide +kernel
      have hl : raw32049step0Labels = raw32049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32049 raw32049Labels permutation346 hz
    mixedMoment B raw32049step0 raw32049step0Labels = mixedMoment B raw32049step1 raw32049step1Labels := by
      have ha : raw32049step1 = (fun i j => raw32049step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32049step1 raw32049step0; decide +kernel
      have hl : raw32049step1Labels = raw32049step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32049step0 raw32049step0Labels permutation34 permutation3
    mixedMoment B raw32049step1 raw32049step1Labels = mixedMoment B raw32049step2 raw32049step2Labels := by
      have ha : raw32049step2 = raw32049step1 := by apply Matrix.ext; unfold raw32049step2 raw32049step1; decide +kernel
      have hl : raw32049step1Labels = labelEmbedding6 ∘ raw32049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32049step1 raw32049step1Labels raw32049step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw32050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32050step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32050step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32050 raw32050Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw32050 raw32050Labels = mixedMoment B raw32050step0 raw32050step0Labels := by
      have hz : ∀ j, raw32050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32050step0 = (fun i j => raw32050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32050step0 raw32050; decide +kernel
      have hl : raw32050step0Labels = raw32050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32050 raw32050Labels permutation346 hz
    mixedMoment B raw32050step0 raw32050step0Labels = mixedMoment B raw32050step1 raw32050step1Labels := by
      have ha : raw32050step1 = (fun i j => raw32050step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32050step1 raw32050step0; decide +kernel
      have hl : raw32050step1Labels = raw32050step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32050step0 raw32050step0Labels permutation32 permutation3
    mixedMoment B raw32050step1 raw32050step1Labels = mixedMoment B raw32050step2 raw32050step2Labels := by
      have ha : raw32050step2 = raw32050step1 := by apply Matrix.ext; unfold raw32050step2 raw32050step1; decide +kernel
      have hl : raw32050step1Labels = labelEmbedding6 ∘ raw32050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32050step1 raw32050step1Labels raw32050step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw32051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32051step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32051step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32051 raw32051Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw32051 raw32051Labels = mixedMoment B raw32051step0 raw32051step0Labels := by
      have ha : raw32051step0 = (fun i j => raw32051 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32051step0 raw32051; decide +kernel
      have hl : raw32051step0Labels = raw32051Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32051 raw32051Labels permutation176 permutation3
    mixedMoment B raw32051step0 raw32051step0Labels = mixedMoment B raw32051step1 raw32051step1Labels := by
      have ha : raw32051step1 = raw32051step0 := by apply Matrix.ext; unfold raw32051step1 raw32051step0; decide +kernel
      have hl : raw32051step0Labels = labelEmbedding6 ∘ raw32051step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32051step0 raw32051step0Labels raw32051step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw32052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw32052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32052 raw32052Labels = mixedMoment B node3824 node3824Labels := by
  calc
    mixedMoment B raw32052 raw32052Labels = mixedMoment B raw32052step0 raw32052step0Labels := by
      have hz : ∀ j, raw32052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32052step0 = (fun i j => raw32052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32052step0 raw32052; decide +kernel
      have hl : raw32052step0Labels = raw32052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32052 raw32052Labels permutation346 hz
    mixedMoment B raw32052step0 raw32052step0Labels = mixedMoment B raw32052step1 raw32052step1Labels := by
      have ha : raw32052step1 = (fun i j => raw32052step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32052step1 raw32052step0; decide +kernel
      have hl : raw32052step1Labels = raw32052step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32052step0 raw32052step0Labels permutation144 permutation3
    mixedMoment B raw32052step1 raw32052step1Labels = mixedMoment B raw32052step2 raw32052step2Labels := by
      have ha : raw32052step2 = -raw32052step1 := by apply Matrix.ext; change ∀ i j, raw32052step2 i j = -(raw32052step1 i j); unfold raw32052step2 raw32052step1; decide +kernel
      have hl : raw32052step2Labels = raw32052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3824 node3824Labels := by rfl

def raw32053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw32053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32053 raw32053Labels = mixedMoment B node3821 node3821Labels := by
  calc
    mixedMoment B raw32053 raw32053Labels = mixedMoment B raw32053step0 raw32053step0Labels := by
      have ha : raw32053step0 = (fun i j => raw32053 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32053step0 raw32053; decide +kernel
      have hl : raw32053step0Labels = raw32053Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32053 raw32053Labels permutation662 permutation3
    mixedMoment B raw32053step0 raw32053step0Labels = mixedMoment B raw32053step1 raw32053step1Labels := by
      have ha : raw32053step1 = -raw32053step0 := by apply Matrix.ext; change ∀ i j, raw32053step1 i j = -(raw32053step0 i j); unfold raw32053step1 raw32053step0; decide +kernel
      have hl : raw32053step1Labels = raw32053step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3821 node3821Labels := by rfl

def raw32054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32054step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw32054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32054 raw32054Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw32054 raw32054Labels = mixedMoment B raw32054step0 raw32054step0Labels := by
      have hz : ∀ j, raw32054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32054step0 = (fun i j => raw32054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32054step0 raw32054; decide +kernel
      have hl : raw32054step0Labels = raw32054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32054 raw32054Labels permutation346 hz
    mixedMoment B raw32054step0 raw32054step0Labels = mixedMoment B raw32054step1 raw32054step1Labels := by
      have ha : raw32054step1 = (fun i j => raw32054step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32054step1 raw32054step0; decide +kernel
      have hl : raw32054step1Labels = raw32054step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32054step0 raw32054step0Labels permutation145 permutation3
    mixedMoment B raw32054step1 raw32054step1Labels = mixedMoment B raw32054step2 raw32054step2Labels := by
      have ha : raw32054step2 = -raw32054step1 := by apply Matrix.ext; change ∀ i j, raw32054step2 i j = -(raw32054step1 i j); unfold raw32054step2 raw32054step1; decide +kernel
      have hl : raw32054step2Labels = raw32054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw32055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32055 raw32055Labels = mixedMoment B node3999 node3999Labels := by
  calc
    mixedMoment B raw32055 raw32055Labels = mixedMoment B raw32055step0 raw32055step0Labels := by
      have hz : ∀ j, raw32055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32055step0 = (fun i j => raw32055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32055step0 raw32055; decide +kernel
      have hl : raw32055step0Labels = raw32055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32055 raw32055Labels permutation346 hz
    mixedMoment B raw32055step0 raw32055step0Labels = mixedMoment B raw32055step1 raw32055step1Labels := by
      have ha : raw32055step1 = (fun i j => raw32055step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32055step1 raw32055step0; decide +kernel
      have hl : raw32055step1Labels = raw32055step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32055step0 raw32055step0Labels permutation32 permutation3
    _ = mixedMoment B node3999 node3999Labels := by rfl

def raw32056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32056 raw32056Labels = mixedMoment B node2330 node2330Labels := by
  calc
    mixedMoment B raw32056 raw32056Labels = mixedMoment B raw32056step0 raw32056step0Labels := by
      have ha : raw32056step0 = (fun i j => raw32056 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32056step0 raw32056; decide +kernel
      have hl : raw32056step0Labels = raw32056Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32056 raw32056Labels permutation160 permutation3
    _ = mixedMoment B node2330 node2330Labels := by rfl

def raw32057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32057 raw32057Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw32057 raw32057Labels = mixedMoment B raw32057step0 raw32057step0Labels := by
      have ha : raw32057step0 = (fun i j => raw32057 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32057step0 raw32057; decide +kernel
      have hl : raw32057step0Labels = raw32057Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32057 raw32057Labels permutation166 permutation3
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw32058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32058 raw32058Labels = mixedMoment B node2593 node2593Labels := by
  calc
    mixedMoment B raw32058 raw32058Labels = mixedMoment B raw32058step0 raw32058step0Labels := by
      have ha : raw32058step0 = (fun i j => raw32058 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32058step0 raw32058; decide +kernel
      have hl : raw32058step0Labels = raw32058Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32058 raw32058Labels permutation160 permutation3
    _ = mixedMoment B node2593 node2593Labels := by rfl

def raw32059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32059 raw32059Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw32059 raw32059Labels = mixedMoment B raw32059step0 raw32059step0Labels := by
      have hz : ∀ j, raw32059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32059step0 = (fun i j => raw32059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32059step0 raw32059; decide +kernel
      have hl : raw32059step0Labels = raw32059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32059 raw32059Labels permutation346 hz
    mixedMoment B raw32059step0 raw32059step0Labels = mixedMoment B raw32059step1 raw32059step1Labels := by
      have ha : raw32059step1 = (fun i j => raw32059step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32059step1 raw32059step0; decide +kernel
      have hl : raw32059step1Labels = raw32059step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32059step0 raw32059step0Labels permutation34 permutation3
    _ = mixedMoment B node2337 node2337Labels := by rfl

def raw32060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32060 raw32060Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw32060 raw32060Labels = mixedMoment B raw32060step0 raw32060step0Labels := by
      have ha : raw32060step0 = (fun i j => raw32060 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32060step0 raw32060; decide +kernel
      have hl : raw32060step0Labels = raw32060Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32060 raw32060Labels permutation178 permutation3
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw32061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32061 raw32061Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw32061 raw32061Labels = mixedMoment B raw32061step0 raw32061step0Labels := by
      have hz : ∀ j, raw32061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32061step0 = (fun i j => raw32061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32061step0 raw32061; decide +kernel
      have hl : raw32061step0Labels = raw32061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32061 raw32061Labels permutation346 hz
    mixedMoment B raw32061step0 raw32061step0Labels = mixedMoment B raw32061step1 raw32061step1Labels := by
      have ha : raw32061step1 = (fun i j => raw32061step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32061step1 raw32061step0; decide +kernel
      have hl : raw32061step1Labels = raw32061step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32061step0 raw32061step0Labels permutation34 permutation3
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw32062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32062 raw32062Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw32062 raw32062Labels = mixedMoment B raw32062step0 raw32062step0Labels := by
      have hz : ∀ j, raw32062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32062step0 = (fun i j => raw32062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32062step0 raw32062; decide +kernel
      have hl : raw32062step0Labels = raw32062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32062 raw32062Labels permutation346 hz
    mixedMoment B raw32062step0 raw32062step0Labels = mixedMoment B raw32062step1 raw32062step1Labels := by
      have ha : raw32062step1 = (fun i j => raw32062step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32062step1 raw32062step0; decide +kernel
      have hl : raw32062step1Labels = raw32062step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32062step0 raw32062step0Labels permutation35 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw32063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32063 raw32063Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw32063 raw32063Labels = mixedMoment B raw32063step0 raw32063step0Labels := by
      have hz : ∀ j, raw32063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32063step0 = (fun i j => raw32063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32063step0 raw32063; decide +kernel
      have hl : raw32063step0Labels = raw32063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32063 raw32063Labels permutation346 hz
    mixedMoment B raw32063step0 raw32063step0Labels = mixedMoment B raw32063step1 raw32063step1Labels := by
      have ha : raw32063step1 = (fun i j => raw32063step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32063step1 raw32063step0; decide +kernel
      have hl : raw32063step1Labels = raw32063step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32063step0 raw32063step0Labels permutation32 permutation3
    _ = mixedMoment B node2337 node2337Labels := by rfl

def raw32064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32064 raw32064Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw32064 raw32064Labels = mixedMoment B raw32064step0 raw32064step0Labels := by
      have ha : raw32064step0 = (fun i j => raw32064 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32064step0 raw32064; decide +kernel
      have hl : raw32064step0Labels = raw32064Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32064 raw32064Labels permutation176 permutation3
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw32065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw32065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw32065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32065 raw32065Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw32065 raw32065Labels = mixedMoment B raw32065step0 raw32065step0Labels := by
      have hz : ∀ j, raw32065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32065step0 = (fun i j => raw32065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32065step0 raw32065; decide +kernel
      have hl : raw32065step0Labels = raw32065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32065 raw32065Labels permutation346 hz
    mixedMoment B raw32065step0 raw32065step0Labels = mixedMoment B raw32065step1 raw32065step1Labels := by
      have ha : raw32065step1 = (fun i j => raw32065step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32065step1 raw32065step0; decide +kernel
      have hl : raw32065step1Labels = raw32065step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32065step0 raw32065step0Labels permutation33 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw32066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32066 raw32066Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw32066 raw32066Labels = mixedMoment B raw32066step0 raw32066step0Labels := by
      have hz : ∀ j, raw32066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32066step0 = (fun i j => raw32066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32066step0 raw32066; decide +kernel
      have hl : raw32066step0Labels = raw32066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32066 raw32066Labels permutation346 hz
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw32067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32067 raw32067Labels = mixedMoment B node5416 node5416Labels := by
  calc
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw32068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32068 raw32068Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw32068 raw32068Labels = mixedMoment B raw32068step0 raw32068step0Labels := by
      have hz : ∀ j, raw32068 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32068step0 = (fun i j => raw32068 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32068step0 raw32068; decide +kernel
      have hl : raw32068step0Labels = raw32068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32068 raw32068Labels permutation346 hz
    mixedMoment B raw32068step0 raw32068step0Labels = mixedMoment B raw32068step1 raw32068step1Labels := by
      have ha : raw32068step1 = (fun i j => raw32068step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32068step1 raw32068step0; decide +kernel
      have hl : raw32068step1Labels = raw32068step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32068step0 raw32068step0Labels permutation34 permutation2
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw32069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32069 raw32069Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw32069 raw32069Labels = mixedMoment B raw32069step0 raw32069step0Labels := by
      have hz : ∀ j, raw32069 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32069step0 = (fun i j => raw32069 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32069step0 raw32069; decide +kernel
      have hl : raw32069step0Labels = raw32069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32069 raw32069Labels permutation346 hz
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw32070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32070 raw32070Labels = mixedMoment B node4968 node4968Labels := by
  calc
    _ = mixedMoment B node4968 node4968Labels := by rfl

def raw32071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32071 raw32071Labels = mixedMoment B node5148 node5148Labels := by
  calc
    mixedMoment B raw32071 raw32071Labels = mixedMoment B raw32071step0 raw32071step0Labels := by
      have ha : raw32071step0 = (fun i j => raw32071 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32071step0 raw32071; decide +kernel
      have hl : raw32071step0Labels = raw32071Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32071 raw32071Labels permutation164 permutation2
    _ = mixedMoment B node5148 node5148Labels := by rfl

def raw32072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32072 raw32072Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw32072 raw32072Labels = mixedMoment B raw32072step0 raw32072step0Labels := by
      have hz : ∀ j, raw32072 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32072step0 = (fun i j => raw32072 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32072step0 raw32072; decide +kernel
      have hl : raw32072step0Labels = raw32072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32072 raw32072Labels permutation346 hz
    mixedMoment B raw32072step0 raw32072step0Labels = mixedMoment B raw32072step1 raw32072step1Labels := by
      have ha : raw32072step1 = (fun i j => raw32072step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32072step1 raw32072step0; decide +kernel
      have hl : raw32072step1Labels = raw32072step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32072step0 raw32072step0Labels permutation34 permutation2
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw32073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32073 raw32073Labels = mixedMoment B node5117 node5117Labels := by
  calc
    mixedMoment B raw32073 raw32073Labels = mixedMoment B raw32073step0 raw32073step0Labels := by
      have ha : raw32073step0 = (fun i j => raw32073 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32073step0 raw32073; decide +kernel
      have hl : raw32073step0Labels = raw32073Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32073 raw32073Labels permutation154 permutation2
    _ = mixedMoment B node5117 node5117Labels := by rfl

def raw32074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32074 raw32074Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw32074 raw32074Labels = mixedMoment B raw32074step0 raw32074step0Labels := by
      have hz : ∀ j, raw32074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32074step0 = (fun i j => raw32074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32074step0 raw32074; decide +kernel
      have hl : raw32074step0Labels = raw32074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32074 raw32074Labels permutation346 hz
    mixedMoment B raw32074step0 raw32074step0Labels = mixedMoment B raw32074step1 raw32074step1Labels := by
      have ha : raw32074step1 = (fun i j => raw32074step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32074step1 raw32074step0; decide +kernel
      have hl : raw32074step1Labels = raw32074step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32074step0 raw32074step0Labels permutation34 permutation2
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw32075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32075 raw32075Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw32075 raw32075Labels = mixedMoment B raw32075step0 raw32075step0Labels := by
      have hz : ∀ j, raw32075 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32075step0 = (fun i j => raw32075 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32075step0 raw32075; decide +kernel
      have hl : raw32075step0Labels = raw32075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32075 raw32075Labels permutation346 hz
    mixedMoment B raw32075step0 raw32075step0Labels = mixedMoment B raw32075step1 raw32075step1Labels := by
      have ha : raw32075step1 = (fun i j => raw32075step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32075step1 raw32075step0; decide +kernel
      have hl : raw32075step1Labels = raw32075step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32075step0 raw32075step0Labels permutation35 permutation2
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw32076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32076step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32076 raw32076Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw32076 raw32076Labels = mixedMoment B raw32076step0 raw32076step0Labels := by
      have hz : ∀ j, raw32076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32076step0 = (fun i j => raw32076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32076step0 raw32076; decide +kernel
      have hl : raw32076step0Labels = raw32076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32076 raw32076Labels permutation346 hz
    mixedMoment B raw32076step0 raw32076step0Labels = mixedMoment B raw32076step1 raw32076step1Labels := by
      have ha : raw32076step1 = (fun i j => raw32076step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32076step1 raw32076step0; decide +kernel
      have hl : raw32076step1Labels = raw32076step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32076step0 raw32076step0Labels permutation58 permutation3
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw32077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32077 raw32077Labels = mixedMoment B node3967 node3967Labels := by
  calc
    mixedMoment B raw32077 raw32077Labels = mixedMoment B raw32077step0 raw32077step0Labels := by
      have ha : raw32077step0 = (fun i j => raw32077 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32077step0 raw32077; decide +kernel
      have hl : raw32077step0Labels = raw32077Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32077 raw32077Labels permutation662 permutation3
    mixedMoment B raw32077step0 raw32077step0Labels = mixedMoment B raw32077step1 raw32077step1Labels := by
      have ha : raw32077step1 = -raw32077step0 := by apply Matrix.ext; change ∀ i j, raw32077step1 i j = -(raw32077step0 i j); unfold raw32077step1 raw32077step0; decide +kernel
      have hl : raw32077step1Labels = raw32077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3967 node3967Labels := by rfl

def raw32078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32078step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32078 raw32078Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw32078 raw32078Labels = mixedMoment B raw32078step0 raw32078step0Labels := by
      have hz : ∀ j, raw32078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32078step0 = (fun i j => raw32078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32078step0 raw32078; decide +kernel
      have hl : raw32078step0Labels = raw32078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32078 raw32078Labels permutation346 hz
    mixedMoment B raw32078step0 raw32078step0Labels = mixedMoment B raw32078step1 raw32078step1Labels := by
      have ha : raw32078step1 = (fun i j => raw32078step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32078step1 raw32078step0; decide +kernel
      have hl : raw32078step1Labels = raw32078step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32078step0 raw32078step0Labels permutation145 permutation3
    mixedMoment B raw32078step1 raw32078step1Labels = mixedMoment B raw32078step2 raw32078step2Labels := by
      have ha : raw32078step2 = -raw32078step1 := by apply Matrix.ext; change ∀ i j, raw32078step2 i j = -(raw32078step1 i j); unfold raw32078step2 raw32078step1; decide +kernel
      have hl : raw32078step2Labels = raw32078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw32079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32079 raw32079Labels = mixedMoment B node4036 node4036Labels := by
  calc
    mixedMoment B raw32079 raw32079Labels = mixedMoment B raw32079step0 raw32079step0Labels := by
      have hz : ∀ j, raw32079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32079step0 = (fun i j => raw32079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32079step0 raw32079; decide +kernel
      have hl : raw32079step0Labels = raw32079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32079 raw32079Labels permutation346 hz
    mixedMoment B raw32079step0 raw32079step0Labels = mixedMoment B raw32079step1 raw32079step1Labels := by
      have ha : raw32079step1 = (fun i j => raw32079step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32079step1 raw32079step0; decide +kernel
      have hl : raw32079step1Labels = raw32079step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32079step0 raw32079step0Labels permutation35 permutation3
    _ = mixedMoment B node4036 node4036Labels := by rfl

def raw32080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32080 raw32080Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw32080 raw32080Labels = mixedMoment B raw32080step0 raw32080step0Labels := by
      have ha : raw32080step0 = (fun i j => raw32080 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32080step0 raw32080; decide +kernel
      have hl : raw32080step0Labels = raw32080Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32080 raw32080Labels permutation164 permutation3
    _ = mixedMoment B node2809 node2809Labels := by rfl

def raw32081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32081 raw32081Labels = mixedMoment B node2927 node2927Labels := by
  calc
    mixedMoment B raw32081 raw32081Labels = mixedMoment B raw32081step0 raw32081step0Labels := by
      have ha : raw32081step0 = (fun i j => raw32081 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32081step0 raw32081; decide +kernel
      have hl : raw32081step0Labels = raw32081Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32081 raw32081Labels permutation164 permutation3
    _ = mixedMoment B node2927 node2927Labels := by rfl

def raw32082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32082 raw32082Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw32082 raw32082Labels = mixedMoment B raw32082step0 raw32082step0Labels := by
      have hz : ∀ j, raw32082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32082step0 = (fun i j => raw32082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32082step0 raw32082; decide +kernel
      have hl : raw32082step0Labels = raw32082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32082 raw32082Labels permutation346 hz
    mixedMoment B raw32082step0 raw32082step0Labels = mixedMoment B raw32082step1 raw32082step1Labels := by
      have ha : raw32082step1 = (fun i j => raw32082step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32082step1 raw32082step0; decide +kernel
      have hl : raw32082step1Labels = raw32082step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32082step0 raw32082step0Labels permutation35 permutation3
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw32083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32083 raw32083Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw32083 raw32083Labels = mixedMoment B raw32083step0 raw32083step0Labels := by
      have ha : raw32083step0 = (fun i j => raw32083 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32083step0 raw32083; decide +kernel
      have hl : raw32083step0Labels = raw32083Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32083 raw32083Labels permutation155 permutation3
    _ = mixedMoment B node2893 node2893Labels := by rfl

def raw32084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw32084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32084 raw32084Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw32084 raw32084Labels = mixedMoment B raw32084step0 raw32084step0Labels := by
      have hz : ∀ j, raw32084 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32084step0 = (fun i j => raw32084 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32084step0 raw32084; decide +kernel
      have hl : raw32084step0Labels = raw32084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32084 raw32084Labels permutation346 hz
    mixedMoment B raw32084step0 raw32084step0Labels = mixedMoment B raw32084step1 raw32084step1Labels := by
      have ha : raw32084step1 = (fun i j => raw32084step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32084step1 raw32084step0; decide +kernel
      have hl : raw32084step1Labels = raw32084step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32084step0 raw32084step0Labels permutation35 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw32085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32085step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32085 raw32085Labels = mixedMoment B node2959 node2959Labels := by
  calc
    mixedMoment B raw32085 raw32085Labels = mixedMoment B raw32085step0 raw32085step0Labels := by
      have hz : ∀ j, raw32085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32085step0 = (fun i j => raw32085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32085step0 raw32085; decide +kernel
      have hl : raw32085step0Labels = raw32085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32085 raw32085Labels permutation346 hz
    mixedMoment B raw32085step0 raw32085step0Labels = mixedMoment B raw32085step1 raw32085step1Labels := by
      have ha : raw32085step1 = (fun i j => raw32085step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32085step1 raw32085step0; decide +kernel
      have hl : raw32085step1Labels = raw32085step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32085step0 raw32085step0Labels permutation35 permutation3
    _ = mixedMoment B node2959 node2959Labels := by rfl

def raw32086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32086step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32086 raw32086Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw32086 raw32086Labels = mixedMoment B raw32086step0 raw32086step0Labels := by
      have ha : raw32086step0 = (fun i j => raw32086 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32086step0 raw32086; decide +kernel
      have hl : raw32086step0Labels = raw32086Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32086 raw32086Labels permutation158 permutation3
    mixedMoment B raw32086step0 raw32086step0Labels = mixedMoment B raw32086step1 raw32086step1Labels := by
      have ha : raw32086step1 = raw32086step0 := by apply Matrix.ext; unfold raw32086step1 raw32086step0; decide +kernel
      have hl : raw32086step0Labels = labelEmbedding6 ∘ raw32086step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32086step0 raw32086step0Labels raw32086step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw32087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32087step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32087 raw32087Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw32087 raw32087Labels = mixedMoment B raw32087step0 raw32087step0Labels := by
      have ha : raw32087step0 = (fun i j => raw32087 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32087step0 raw32087; decide +kernel
      have hl : raw32087step0Labels = raw32087Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32087 raw32087Labels permutation158 permutation3
    mixedMoment B raw32087step0 raw32087step0Labels = mixedMoment B raw32087step1 raw32087step1Labels := by
      have ha : raw32087step1 = raw32087step0 := by apply Matrix.ext; unfold raw32087step1 raw32087step0; decide +kernel
      have hl : raw32087step0Labels = labelEmbedding6 ∘ raw32087step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32087step0 raw32087step0Labels raw32087step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw32088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw32088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32088step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32088 raw32088Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32088 raw32088Labels = mixedMoment B raw32088step0 raw32088step0Labels := by
      have hz : ∀ j, raw32088 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32088step0 = (fun i j => raw32088 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32088step0 raw32088; decide +kernel
      have hl : raw32088step0Labels = raw32088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32088 raw32088Labels permutation520 hz
    mixedMoment B raw32088step0 raw32088step0Labels = mixedMoment B raw32088step1 raw32088step1Labels := by
      have ha : raw32088step1 = (fun i j => raw32088step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32088step1 raw32088step0; decide +kernel
      have hl : raw32088step1Labels = raw32088step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32088step0 raw32088step0Labels permutation34 permutation3
    mixedMoment B raw32088step1 raw32088step1Labels = mixedMoment B raw32088step2 raw32088step2Labels := by
      have ha : raw32088step2 = raw32088step1 := by apply Matrix.ext; unfold raw32088step2 raw32088step1; decide +kernel
      have hl : raw32088step1Labels = labelEmbedding6 ∘ raw32088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32088step1 raw32088step1Labels raw32088step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw32089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32089step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32089 raw32089Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw32089 raw32089Labels = mixedMoment B raw32089step0 raw32089step0Labels := by
      have ha : raw32089step0 = (fun i j => raw32089 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32089step0 raw32089; decide +kernel
      have hl : raw32089step0Labels = raw32089Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32089 raw32089Labels permutation162 permutation3
    mixedMoment B raw32089step0 raw32089step0Labels = mixedMoment B raw32089step1 raw32089step1Labels := by
      have ha : raw32089step1 = raw32089step0 := by apply Matrix.ext; unfold raw32089step1 raw32089step0; decide +kernel
      have hl : raw32089step0Labels = labelEmbedding6 ∘ raw32089step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32089step0 raw32089step0Labels raw32089step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw32090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32090step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32090 raw32090Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw32090 raw32090Labels = mixedMoment B raw32090step0 raw32090step0Labels := by
      have hz : ∀ j, raw32090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32090step0 = (fun i j => raw32090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32090step0 raw32090; decide +kernel
      have hl : raw32090step0Labels = raw32090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32090 raw32090Labels permutation346 hz
    mixedMoment B raw32090step0 raw32090step0Labels = mixedMoment B raw32090step1 raw32090step1Labels := by
      have ha : raw32090step1 = (fun i j => raw32090step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32090step1 raw32090step0; decide +kernel
      have hl : raw32090step1Labels = raw32090step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32090step0 raw32090step0Labels permutation34 permutation3
    mixedMoment B raw32090step1 raw32090step1Labels = mixedMoment B raw32090step2 raw32090step2Labels := by
      have ha : raw32090step2 = raw32090step1 := by apply Matrix.ext; unfold raw32090step2 raw32090step1; decide +kernel
      have hl : raw32090step1Labels = labelEmbedding6 ∘ raw32090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32090step1 raw32090step1Labels raw32090step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw32091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32091step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32091 raw32091Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw32091 raw32091Labels = mixedMoment B raw32091step0 raw32091step0Labels := by
      have hz : ∀ j, raw32091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32091step0 = (fun i j => raw32091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32091step0 raw32091; decide +kernel
      have hl : raw32091step0Labels = raw32091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32091 raw32091Labels permutation346 hz
    mixedMoment B raw32091step0 raw32091step0Labels = mixedMoment B raw32091step1 raw32091step1Labels := by
      have ha : raw32091step1 = (fun i j => raw32091step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32091step1 raw32091step0; decide +kernel
      have hl : raw32091step1Labels = raw32091step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32091step0 raw32091step0Labels permutation34 permutation3
    mixedMoment B raw32091step1 raw32091step1Labels = mixedMoment B raw32091step2 raw32091step2Labels := by
      have ha : raw32091step2 = raw32091step1 := by apply Matrix.ext; unfold raw32091step2 raw32091step1; decide +kernel
      have hl : raw32091step1Labels = labelEmbedding6 ∘ raw32091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32091step1 raw32091step1Labels raw32091step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw32092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32092step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32092 raw32092Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw32092 raw32092Labels = mixedMoment B raw32092step0 raw32092step0Labels := by
      have ha : raw32092step0 = (fun i j => raw32092 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32092step0 raw32092; decide +kernel
      have hl : raw32092step0Labels = raw32092Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32092 raw32092Labels permutation178 permutation3
    mixedMoment B raw32092step0 raw32092step0Labels = mixedMoment B raw32092step1 raw32092step1Labels := by
      have ha : raw32092step1 = raw32092step0 := by apply Matrix.ext; unfold raw32092step1 raw32092step0; decide +kernel
      have hl : raw32092step0Labels = labelEmbedding6 ∘ raw32092step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32092step0 raw32092step0Labels raw32092step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5039 node5039Labels := by rfl

def raw32093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw32093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32093step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32093step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32093 raw32093Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw32093 raw32093Labels = mixedMoment B raw32093step0 raw32093step0Labels := by
      have hz : ∀ j, raw32093 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32093step0 = (fun i j => raw32093 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32093step0 raw32093; decide +kernel
      have hl : raw32093step0Labels = raw32093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32093 raw32093Labels permutation520 hz
    mixedMoment B raw32093step0 raw32093step0Labels = mixedMoment B raw32093step1 raw32093step1Labels := by
      have hz : ∀ j, raw32093step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32093step1 = (fun i j => raw32093step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32093step1 raw32093step0; decide +kernel
      have hl : raw32093step1Labels = raw32093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32093step0 raw32093step0Labels permutation80 hz
    mixedMoment B raw32093step1 raw32093step1Labels = mixedMoment B raw32093step2 raw32093step2Labels := by
      have ha : raw32093step2 = (fun i j => raw32093step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32093step2 raw32093step1; decide +kernel
      have hl : raw32093step2Labels = raw32093step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32093step1 raw32093step1Labels permutation8 permutation3
    mixedMoment B raw32093step2 raw32093step2Labels = mixedMoment B raw32093step3 raw32093step3Labels := by
      have ha : raw32093step3 = raw32093step2 := by apply Matrix.ext; unfold raw32093step3 raw32093step2; decide +kernel
      have hl : raw32093step2Labels = labelEmbedding6 ∘ raw32093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32093step2 raw32093step2Labels raw32093step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw32094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32094step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32094step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32094 raw32094Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32094 raw32094Labels = mixedMoment B raw32094step0 raw32094step0Labels := by
      have hz : ∀ j, raw32094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32094step0 = (fun i j => raw32094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32094step0 raw32094; decide +kernel
      have hl : raw32094step0Labels = raw32094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32094 raw32094Labels permutation346 hz
    mixedMoment B raw32094step0 raw32094step0Labels = mixedMoment B raw32094step1 raw32094step1Labels := by
      have ha : raw32094step1 = (fun i j => raw32094step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32094step1 raw32094step0; decide +kernel
      have hl : raw32094step1Labels = raw32094step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32094step0 raw32094step0Labels permutation37 permutation3
    mixedMoment B raw32094step1 raw32094step1Labels = mixedMoment B raw32094step2 raw32094step2Labels := by
      have ha : raw32094step2 = raw32094step1 := by apply Matrix.ext; unfold raw32094step2 raw32094step1; decide +kernel
      have hl : raw32094step1Labels = labelEmbedding6 ∘ raw32094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32094step1 raw32094step1Labels raw32094step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw32095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32095 raw32095Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw32095 raw32095Labels = mixedMoment B raw32095step0 raw32095step0Labels := by
      have ha : raw32095step0 = (fun i j => raw32095 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32095step0 raw32095; decide +kernel
      have hl : raw32095step0Labels = raw32095Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32095 raw32095Labels permutation158 permutation3
    _ = mixedMoment B node922 node922Labels := by rfl

def raw32096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32096 raw32096Labels = mixedMoment B node2332 node2332Labels := by
  calc
    mixedMoment B raw32096 raw32096Labels = mixedMoment B raw32096step0 raw32096step0Labels := by
      have ha : raw32096step0 = (fun i j => raw32096 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32096step0 raw32096; decide +kernel
      have hl : raw32096step0Labels = raw32096Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32096 raw32096Labels permutation158 permutation3
    _ = mixedMoment B node2332 node2332Labels := by rfl

def raw32097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw32097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32097step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32097 raw32097Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw32097 raw32097Labels = mixedMoment B raw32097step0 raw32097step0Labels := by
      have hz : ∀ j, raw32097 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32097step0 = (fun i j => raw32097 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32097step0 raw32097; decide +kernel
      have hl : raw32097step0Labels = raw32097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32097 raw32097Labels permutation520 hz
    mixedMoment B raw32097step0 raw32097step0Labels = mixedMoment B raw32097step1 raw32097step1Labels := by
      have ha : raw32097step1 = (fun i j => raw32097step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32097step1 raw32097step0; decide +kernel
      have hl : raw32097step1Labels = raw32097step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32097step0 raw32097step0Labels permutation34 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw32098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32098 raw32098Labels = mixedMoment B node2593 node2593Labels := by
  calc
    mixedMoment B raw32098 raw32098Labels = mixedMoment B raw32098step0 raw32098step0Labels := by
      have ha : raw32098step0 = (fun i j => raw32098 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32098step0 raw32098; decide +kernel
      have hl : raw32098step0Labels = raw32098Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32098 raw32098Labels permutation162 permutation3
    _ = mixedMoment B node2593 node2593Labels := by rfl

def raw32099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32099step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32099 raw32099Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw32099 raw32099Labels = mixedMoment B raw32099step0 raw32099step0Labels := by
      have hz : ∀ j, raw32099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32099step0 = (fun i j => raw32099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32099step0 raw32099; decide +kernel
      have hl : raw32099step0Labels = raw32099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32099 raw32099Labels permutation346 hz
    mixedMoment B raw32099step0 raw32099step0Labels = mixedMoment B raw32099step1 raw32099step1Labels := by
      have ha : raw32099step1 = (fun i j => raw32099step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32099step1 raw32099step0; decide +kernel
      have hl : raw32099step1Labels = raw32099step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32099step0 raw32099step0Labels permutation34 permutation3
    _ = mixedMoment B node933 node933Labels := by rfl

def raw32100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32100 raw32100Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw32100 raw32100Labels = mixedMoment B raw32100step0 raw32100step0Labels := by
      have hz : ∀ j, raw32100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32100step0 = (fun i j => raw32100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32100step0 raw32100; decide +kernel
      have hl : raw32100step0Labels = raw32100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32100 raw32100Labels permutation346 hz
    mixedMoment B raw32100step0 raw32100step0Labels = mixedMoment B raw32100step1 raw32100step1Labels := by
      have ha : raw32100step1 = (fun i j => raw32100step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32100step1 raw32100step0; decide +kernel
      have hl : raw32100step1Labels = raw32100step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32100step0 raw32100step0Labels permutation34 permutation3
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw32101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32101 raw32101Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw32101 raw32101Labels = mixedMoment B raw32101step0 raw32101step0Labels := by
      have ha : raw32101step0 = (fun i j => raw32101 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32101step0 raw32101; decide +kernel
      have hl : raw32101step0Labels = raw32101Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32101 raw32101Labels permutation178 permutation3
    _ = mixedMoment B node2432 node2432Labels := by rfl

def raw32102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw32102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw32102step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw32102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32102 raw32102Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw32102 raw32102Labels = mixedMoment B raw32102step0 raw32102step0Labels := by
      have hz : ∀ j, raw32102 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32102step0 = (fun i j => raw32102 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32102step0 raw32102; decide +kernel
      have hl : raw32102step0Labels = raw32102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32102 raw32102Labels permutation520 hz
    mixedMoment B raw32102step0 raw32102step0Labels = mixedMoment B raw32102step1 raw32102step1Labels := by
      have hz : ∀ j, raw32102step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32102step1 = (fun i j => raw32102step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32102step1 raw32102step0; decide +kernel
      have hl : raw32102step1Labels = raw32102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32102step0 raw32102step0Labels permutation80 hz
    mixedMoment B raw32102step1 raw32102step1Labels = mixedMoment B raw32102step2 raw32102step2Labels := by
      have ha : raw32102step2 = (fun i j => raw32102step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32102step2 raw32102step1; decide +kernel
      have hl : raw32102step2Labels = raw32102step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32102step1 raw32102step1Labels permutation8 permutation3
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw32103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw32103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32103 raw32103Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw32103 raw32103Labels = mixedMoment B raw32103step0 raw32103step0Labels := by
      have hz : ∀ j, raw32103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32103step0 = (fun i j => raw32103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32103step0 raw32103; decide +kernel
      have hl : raw32103step0Labels = raw32103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32103 raw32103Labels permutation346 hz
    mixedMoment B raw32103step0 raw32103step0Labels = mixedMoment B raw32103step1 raw32103step1Labels := by
      have ha : raw32103step1 = (fun i j => raw32103step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32103step1 raw32103step0; decide +kernel
      have hl : raw32103step1Labels = raw32103step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32103step0 raw32103step0Labels permutation37 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw32104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32104 raw32104Labels = mixedMoment B node4969 node4969Labels := by
  calc
    _ = mixedMoment B node4969 node4969Labels := by rfl

def raw32105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw32105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32105 raw32105Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw32105 raw32105Labels = mixedMoment B raw32105step0 raw32105step0Labels := by
      have ha : raw32105step0 = (fun i j => raw32105 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32105step0 raw32105; decide +kernel
      have hl : raw32105step0Labels = raw32105Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32105 raw32105Labels permutation164 permutation2
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw32106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw32106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32106 raw32106Labels = mixedMoment B node5166 node5166Labels := by
  calc
    mixedMoment B raw32106 raw32106Labels = mixedMoment B raw32106step0 raw32106step0Labels := by
      have ha : raw32106step0 = (fun i j => raw32106 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32106step0 raw32106; decide +kernel
      have hl : raw32106step0Labels = raw32106Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32106 raw32106Labels permutation153 permutation2
    _ = mixedMoment B node5166 node5166Labels := by rfl

def raw32107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw32107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32107 raw32107Labels = mixedMoment B node4978 node4978Labels := by
  calc
    mixedMoment B raw32107 raw32107Labels = mixedMoment B raw32107step0 raw32107step0Labels := by
      have hz : ∀ j, raw32107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32107step0 = (fun i j => raw32107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32107step0 raw32107; decide +kernel
      have hl : raw32107step0Labels = raw32107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32107 raw32107Labels permutation346 hz
    mixedMoment B raw32107step0 raw32107step0Labels = mixedMoment B raw32107step1 raw32107step1Labels := by
      have ha : raw32107step1 = (fun i j => raw32107step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32107step1 raw32107step0; decide +kernel
      have hl : raw32107step1Labels = raw32107step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32107step0 raw32107step0Labels permutation34 permutation2
    _ = mixedMoment B node4978 node4978Labels := by rfl

def raw32108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw32108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32108 raw32108Labels = mixedMoment B node5118 node5118Labels := by
  calc
    mixedMoment B raw32108 raw32108Labels = mixedMoment B raw32108step0 raw32108step0Labels := by
      have ha : raw32108step0 = (fun i j => raw32108 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32108step0 raw32108; decide +kernel
      have hl : raw32108step0Labels = raw32108Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32108 raw32108Labels permutation154 permutation2
    _ = mixedMoment B node5118 node5118Labels := by rfl

def raw32109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw32109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32109 raw32109Labels = mixedMoment B node5156 node5156Labels := by
  calc
    mixedMoment B raw32109 raw32109Labels = mixedMoment B raw32109step0 raw32109step0Labels := by
      have hz : ∀ j, raw32109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32109step0 = (fun i j => raw32109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32109step0 raw32109; decide +kernel
      have hl : raw32109step0Labels = raw32109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32109 raw32109Labels permutation346 hz
    mixedMoment B raw32109step0 raw32109step0Labels = mixedMoment B raw32109step1 raw32109step1Labels := by
      have ha : raw32109step1 = (fun i j => raw32109step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32109step1 raw32109step0; decide +kernel
      have hl : raw32109step1Labels = raw32109step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32109step0 raw32109step0Labels permutation34 permutation2
    _ = mixedMoment B node5156 node5156Labels := by rfl

def raw32110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32110 raw32110Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw32110 raw32110Labels = mixedMoment B raw32110step0 raw32110step0Labels := by
      have hz : ∀ j, raw32110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32110step0 = (fun i j => raw32110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32110step0 raw32110; decide +kernel
      have hl : raw32110step0Labels = raw32110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32110 raw32110Labels permutation346 hz
    mixedMoment B raw32110step0 raw32110step0Labels = mixedMoment B raw32110step1 raw32110step1Labels := by
      have ha : raw32110step1 = (fun i j => raw32110step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32110step1 raw32110step0; decide +kernel
      have hl : raw32110step1Labels = raw32110step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32110step0 raw32110step0Labels permutation37 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw32111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw32111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw32111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32111step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32111 raw32111Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw32111 raw32111Labels = mixedMoment B raw32111step0 raw32111step0Labels := by
      have hz : ∀ j, raw32111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32111step0 = (fun i j => raw32111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32111step0 raw32111; decide +kernel
      have hl : raw32111step0Labels = raw32111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32111 raw32111Labels permutation346 hz
    mixedMoment B raw32111step0 raw32111step0Labels = mixedMoment B raw32111step1 raw32111step1Labels := by
      have ha : raw32111step1 = (fun i j => raw32111step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32111step1 raw32111step0; decide +kernel
      have hl : raw32111step1Labels = raw32111step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32111step0 raw32111step0Labels permutation33 permutation2
    _ = mixedMoment B node4973 node4973Labels := by rfl

def raw32112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw32112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32112 raw32112Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw32112 raw32112Labels = mixedMoment B raw32112step0 raw32112step0Labels := by
      have ha : raw32112step0 = (fun i j => raw32112 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32112step0 raw32112; decide +kernel
      have hl : raw32112step0Labels = raw32112Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32112 raw32112Labels permutation153 permutation2
    _ = mixedMoment B node5114 node5114Labels := by rfl

def raw32113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw32113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw32113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32113step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32113 raw32113Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw32113 raw32113Labels = mixedMoment B raw32113step0 raw32113step0Labels := by
      have hz : ∀ j, raw32113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32113step0 = (fun i j => raw32113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32113step0 raw32113; decide +kernel
      have hl : raw32113step0Labels = raw32113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32113 raw32113Labels permutation346 hz
    mixedMoment B raw32113step0 raw32113step0Labels = mixedMoment B raw32113step1 raw32113step1Labels := by
      have ha : raw32113step1 = (fun i j => raw32113step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32113step1 raw32113step0; decide +kernel
      have hl : raw32113step1Labels = raw32113step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32113step0 raw32113step0Labels permutation33 permutation2
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw32114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32114 raw32114Labels = mixedMoment B node2804 node2804Labels := by
  calc
    mixedMoment B raw32114 raw32114Labels = mixedMoment B raw32114step0 raw32114step0Labels := by
      have ha : raw32114step0 = (fun i j => raw32114 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32114step0 raw32114; decide +kernel
      have hl : raw32114step0Labels = raw32114Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32114 raw32114Labels permutation164 permutation3
    _ = mixedMoment B node2804 node2804Labels := by rfl

def raw32115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32115 raw32115Labels = mixedMoment B node2908 node2908Labels := by
  calc
    mixedMoment B raw32115 raw32115Labels = mixedMoment B raw32115step0 raw32115step0Labels := by
      have ha : raw32115step0 = (fun i j => raw32115 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32115step0 raw32115; decide +kernel
      have hl : raw32115step0Labels = raw32115Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32115 raw32115Labels permutation164 permutation3
    _ = mixedMoment B node2908 node2908Labels := by rfl

def raw32116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32116 raw32116Labels = mixedMoment B node2953 node2953Labels := by
  calc
    mixedMoment B raw32116 raw32116Labels = mixedMoment B raw32116step0 raw32116step0Labels := by
      have ha : raw32116step0 = (fun i j => raw32116 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32116step0 raw32116; decide +kernel
      have hl : raw32116step0Labels = raw32116Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32116 raw32116Labels permutation164 permutation3
    _ = mixedMoment B node2953 node2953Labels := by rfl

def raw32117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32117 raw32117Labels = mixedMoment B node2805 node2805Labels := by
  calc
    mixedMoment B raw32117 raw32117Labels = mixedMoment B raw32117step0 raw32117step0Labels := by
      have hz : ∀ j, raw32117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32117step0 = (fun i j => raw32117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32117step0 raw32117; decide +kernel
      have hl : raw32117step0Labels = raw32117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32117 raw32117Labels permutation346 hz
    mixedMoment B raw32117step0 raw32117step0Labels = mixedMoment B raw32117step1 raw32117step1Labels := by
      have ha : raw32117step1 = (fun i j => raw32117step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32117step1 raw32117step0; decide +kernel
      have hl : raw32117step1Labels = raw32117step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32117step0 raw32117step0Labels permutation34 permutation3
    _ = mixedMoment B node2805 node2805Labels := by rfl

def raw32118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32118 raw32118Labels = mixedMoment B node2891 node2891Labels := by
  calc
    mixedMoment B raw32118 raw32118Labels = mixedMoment B raw32118step0 raw32118step0Labels := by
      have ha : raw32118step0 = (fun i j => raw32118 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32118step0 raw32118; decide +kernel
      have hl : raw32118step0Labels = raw32118Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32118 raw32118Labels permutation154 permutation3
    _ = mixedMoment B node2891 node2891Labels := by rfl

def raw32119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw32119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32119 raw32119Labels = mixedMoment B node2911 node2911Labels := by
  calc
    mixedMoment B raw32119 raw32119Labels = mixedMoment B raw32119step0 raw32119step0Labels := by
      have hz : ∀ j, raw32119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32119step0 = (fun i j => raw32119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32119step0 raw32119; decide +kernel
      have hl : raw32119step0Labels = raw32119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32119 raw32119Labels permutation346 hz
    mixedMoment B raw32119step0 raw32119step0Labels = mixedMoment B raw32119step1 raw32119step1Labels := by
      have ha : raw32119step1 = (fun i j => raw32119step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32119step1 raw32119step0; decide +kernel
      have hl : raw32119step1Labels = raw32119step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32119step0 raw32119step0Labels permutation34 permutation3
    _ = mixedMoment B node2911 node2911Labels := by rfl

def raw32120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32120 raw32120Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw32120 raw32120Labels = mixedMoment B raw32120step0 raw32120step0Labels := by
      have hz : ∀ j, raw32120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32120step0 = (fun i j => raw32120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32120step0 raw32120; decide +kernel
      have hl : raw32120step0Labels = raw32120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32120 raw32120Labels permutation346 hz
    mixedMoment B raw32120step0 raw32120step0Labels = mixedMoment B raw32120step1 raw32120step1Labels := by
      have ha : raw32120step1 = (fun i j => raw32120step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32120step1 raw32120step0; decide +kernel
      have hl : raw32120step1Labels = raw32120step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32120step0 raw32120step0Labels permutation35 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw32121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw32121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw32121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32121 raw32121Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw32121 raw32121Labels = mixedMoment B raw32121step0 raw32121step0Labels := by
      have hz : ∀ j, raw32121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32121step0 = (fun i j => raw32121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32121step0 raw32121; decide +kernel
      have hl : raw32121step0Labels = raw32121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32121 raw32121Labels permutation346 hz
    mixedMoment B raw32121step0 raw32121step0Labels = mixedMoment B raw32121step1 raw32121step1Labels := by
      have ha : raw32121step1 = (fun i j => raw32121step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32121step1 raw32121step0; decide +kernel
      have hl : raw32121step1Labels = raw32121step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32121step0 raw32121step0Labels permutation32 permutation3
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw32122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw32122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32122 raw32122Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw32122 raw32122Labels = mixedMoment B raw32122step0 raw32122step0Labels := by
      have ha : raw32122step0 = (fun i j => raw32122 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32122step0 raw32122; decide +kernel
      have hl : raw32122step0Labels = raw32122Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32122 raw32122Labels permutation152 permutation3
    _ = mixedMoment B node2896 node2896Labels := by rfl

def raw32123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw32123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw32123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32123 raw32123Labels = mixedMoment B node2963 node2963Labels := by
  calc
    mixedMoment B raw32123 raw32123Labels = mixedMoment B raw32123step0 raw32123step0Labels := by
      have hz : ∀ j, raw32123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32123step0 = (fun i j => raw32123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32123step0 raw32123; decide +kernel
      have hl : raw32123step0Labels = raw32123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32123 raw32123Labels permutation346 hz
    mixedMoment B raw32123step0 raw32123step0Labels = mixedMoment B raw32123step1 raw32123step1Labels := by
      have ha : raw32123step1 = (fun i j => raw32123step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32123step1 raw32123step0; decide +kernel
      have hl : raw32123step1Labels = raw32123step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32123step0 raw32123step0Labels permutation33 permutation3
    _ = mixedMoment B node2963 node2963Labels := by rfl

def raw32124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32124 raw32124Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw32124 raw32124Labels = mixedMoment B raw32124step0 raw32124step0Labels := by
      have hz : ∀ j, raw32124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32124step0 = (fun i j => raw32124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32124step0 raw32124; decide +kernel
      have hl : raw32124step0Labels = raw32124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32124 raw32124Labels permutation346 hz
    mixedMoment B raw32124step0 raw32124step0Labels = mixedMoment B raw32124step1 raw32124step1Labels := by
      have ha : raw32124step1 = (fun i j => raw32124step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32124step1 raw32124step0; decide +kernel
      have hl : raw32124step1Labels = raw32124step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32124step0 raw32124step0Labels permutation144 permutation2
    mixedMoment B raw32124step1 raw32124step1Labels = mixedMoment B raw32124step2 raw32124step2Labels := by
      have ha : raw32124step2 = -raw32124step1 := by apply Matrix.ext; change ∀ i j, raw32124step2 i j = -(raw32124step1 i j); unfold raw32124step2 raw32124step1; decide +kernel
      have hl : raw32124step2Labels = raw32124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw32125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw32125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32125 raw32125Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw32125 raw32125Labels = mixedMoment B raw32125step0 raw32125step0Labels := by
      have ha : raw32125step0 = (fun i j => raw32125 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32125step0 raw32125; decide +kernel
      have hl : raw32125step0Labels = raw32125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32125 raw32125Labels permutation664 permutation2
    mixedMoment B raw32125step0 raw32125step0Labels = mixedMoment B raw32125step1 raw32125step1Labels := by
      have ha : raw32125step1 = -raw32125step0 := by apply Matrix.ext; change ∀ i j, raw32125step1 i j = -(raw32125step0 i j); unfold raw32125step1 raw32125step0; decide +kernel
      have hl : raw32125step1Labels = raw32125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw32126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32126step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32126step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32126 raw32126Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw32126 raw32126Labels = mixedMoment B raw32126step0 raw32126step0Labels := by
      have hz : ∀ j, raw32126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32126step0 = (fun i j => raw32126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32126step0 raw32126; decide +kernel
      have hl : raw32126step0Labels = raw32126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32126 raw32126Labels permutation346 hz
    mixedMoment B raw32126step0 raw32126step0Labels = mixedMoment B raw32126step1 raw32126step1Labels := by
      have ha : raw32126step1 = (fun i j => raw32126step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32126step1 raw32126step0; decide +kernel
      have hl : raw32126step1Labels = raw32126step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32126step0 raw32126step0Labels permutation145 permutation7
    mixedMoment B raw32126step1 raw32126step1Labels = mixedMoment B raw32126step2 raw32126step2Labels := by
      have ha : raw32126step2 = raw32126step1 := by apply Matrix.ext; unfold raw32126step2 raw32126step1; decide +kernel
      have hl : raw32126step1Labels = labelEmbedding10 ∘ raw32126step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32126step1 raw32126step1Labels raw32126step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw32127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32127 raw32127Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw32127 raw32127Labels = mixedMoment B raw32127step0 raw32127step0Labels := by
      have hz : ∀ j, raw32127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32127step0 = (fun i j => raw32127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32127step0 raw32127; decide +kernel
      have hl : raw32127step0Labels = raw32127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32127 raw32127Labels permutation346 hz
    mixedMoment B raw32127step0 raw32127step0Labels = mixedMoment B raw32127step1 raw32127step1Labels := by
      have ha : raw32127step1 = (fun i j => raw32127step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32127step1 raw32127step0; decide +kernel
      have hl : raw32127step1Labels = raw32127step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32127step0 raw32127step0Labels permutation145 permutation2
    mixedMoment B raw32127step1 raw32127step1Labels = mixedMoment B raw32127step2 raw32127step2Labels := by
      have ha : raw32127step2 = -raw32127step1 := by apply Matrix.ext; change ∀ i j, raw32127step2 i j = -(raw32127step1 i j); unfold raw32127step2 raw32127step1; decide +kernel
      have hl : raw32127step2Labels = raw32127step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
