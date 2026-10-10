import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.ExtraNodes

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39808Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw39808step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39808step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39808 raw39808Labels = mixedMoment B node364 node364Labels := by
  calc
    mixedMoment B raw39808 raw39808Labels = mixedMoment B raw39808step0 raw39808step0Labels := by
      have hz : ∀ j, raw39808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39808step0 = (fun i j => raw39808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39808step0 raw39808; decide +kernel
      have hl : raw39808step0Labels = raw39808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39808 raw39808Labels permutation434 hz
    mixedMoment B raw39808step0 raw39808step0Labels = mixedMoment B raw39808step1 raw39808step1Labels := by
      have ha : raw39808step1 = (fun i j => raw39808step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39808step1 raw39808step0; decide +kernel
      have hl : raw39808step1Labels = raw39808step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39808step0 raw39808step0Labels permutation108 permutation4
    _ = mixedMoment B node364 node364Labels := by rfl

def raw39809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39809Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39809step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39809 raw39809Labels = mixedMoment B node481 node481Labels := by
  calc
    mixedMoment B raw39809 raw39809Labels = mixedMoment B raw39809step0 raw39809step0Labels := by
      have ha : raw39809step0 = (fun i j => raw39809 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39809step0 raw39809; decide +kernel
      have hl : raw39809step0Labels = raw39809Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39809 raw39809Labels permutation158 permutation2
    _ = mixedMoment B node481 node481Labels := by rfl

def raw39810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39810Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39810step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39810 raw39810Labels = mixedMoment B node443 node443Labels := by
  calc
    mixedMoment B raw39810 raw39810Labels = mixedMoment B raw39810step0 raw39810step0Labels := by
      have ha : raw39810step0 = (fun i j => raw39810 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39810step0 raw39810; decide +kernel
      have hl : raw39810step0Labels = raw39810Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39810 raw39810Labels permutation421 permutation6
    _ = mixedMoment B node443 node443Labels := by rfl

def raw39811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39811Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39811step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39811 raw39811Labels = mixedMoment B node440 node440Labels := by
  calc
    mixedMoment B raw39811 raw39811Labels = mixedMoment B raw39811step0 raw39811step0Labels := by
      have ha : raw39811step0 = (fun i j => raw39811 (permutation422 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39811step0 raw39811; decide +kernel
      have hl : raw39811step0Labels = raw39811Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39811 raw39811Labels permutation422 permutation6
    _ = mixedMoment B node440 node440Labels := by rfl

def raw39812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39812Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39812step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39812 raw39812Labels = mixedMoment B node480 node480Labels := by
  calc
    mixedMoment B raw39812 raw39812Labels = mixedMoment B raw39812step0 raw39812step0Labels := by
      have ha : raw39812step0 = (fun i j => raw39812 (permutation387 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39812step0 raw39812; decide +kernel
      have hl : raw39812step0Labels = raw39812Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39812 raw39812Labels permutation387 permutation6
    _ = mixedMoment B node480 node480Labels := by rfl

def raw39813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39813Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39813step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39813 raw39813Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw39813 raw39813Labels = mixedMoment B raw39813step0 raw39813step0Labels := by
      have hz : ∀ j, raw39813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39813step0 = (fun i j => raw39813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39813step0 raw39813; decide +kernel
      have hl : raw39813step0Labels = raw39813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39813 raw39813Labels permutation434 hz
    _ = mixedMoment B node489 node489Labels := by rfl

def raw39814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39814Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39814step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39814 raw39814Labels = mixedMoment B node478 node478Labels := by
  calc
    mixedMoment B raw39814 raw39814Labels = mixedMoment B raw39814step0 raw39814step0Labels := by
      have ha : raw39814step0 = (fun i j => raw39814 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39814step0 raw39814; decide +kernel
      have hl : raw39814step0Labels = raw39814Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39814 raw39814Labels permutation158 permutation2
    _ = mixedMoment B node478 node478Labels := by rfl

def raw39815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39815Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39815step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39815step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39815step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39815 raw39815Labels = mixedMoment B node391 node391Labels := by
  calc
    mixedMoment B raw39815 raw39815Labels = mixedMoment B raw39815step0 raw39815step0Labels := by
      have hz : ∀ j, raw39815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39815step0 = (fun i j => raw39815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39815step0 raw39815; decide +kernel
      have hl : raw39815step0Labels = raw39815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39815 raw39815Labels permutation434 hz
    mixedMoment B raw39815step0 raw39815step0Labels = mixedMoment B raw39815step1 raw39815step1Labels := by
      have hz : ∀ j, raw39815step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39815step1 = (fun i j => raw39815step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39815step1 raw39815step0; decide +kernel
      have hl : raw39815step1Labels = raw39815step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39815step0 raw39815step0Labels permutation80 hz
    mixedMoment B raw39815step1 raw39815step1Labels = mixedMoment B raw39815step2 raw39815step2Labels := by
      have ha : raw39815step2 = (fun i j => raw39815step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39815step2 raw39815step1; decide +kernel
      have hl : raw39815step2Labels = raw39815step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39815step1 raw39815step1Labels permutation23 permutation6
    _ = mixedMoment B node391 node391Labels := by rfl

def raw39816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39816Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39816step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39816step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39816step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39816 raw39816Labels = mixedMoment B node148 node148Labels := by
  calc
    mixedMoment B raw39816 raw39816Labels = mixedMoment B raw39816step0 raw39816step0Labels := by
      have hz : ∀ j, raw39816 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39816step0 = (fun i j => raw39816 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39816step0 raw39816; decide +kernel
      have hl : raw39816step0Labels = raw39816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39816 raw39816Labels permutation434 hz
    mixedMoment B raw39816step0 raw39816step0Labels = mixedMoment B raw39816step1 raw39816step1Labels := by
      have hz : ∀ j, raw39816step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39816step1 = (fun i j => raw39816step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39816step1 raw39816step0; decide +kernel
      have hl : raw39816step1Labels = raw39816step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39816step0 raw39816step0Labels permutation80 hz
    mixedMoment B raw39816step1 raw39816step1Labels = mixedMoment B raw39816step2 raw39816step2Labels := by
      have ha : raw39816step2 = (fun i j => raw39816step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39816step2 raw39816step1; decide +kernel
      have hl : raw39816step2Labels = raw39816step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39816step1 raw39816step1Labels permutation28 permutation6
    _ = mixedMoment B node148 node148Labels := by rfl

def raw39817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39817Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39817step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39817step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39817 raw39817Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39817 raw39817Labels = mixedMoment B raw39817step0 raw39817step0Labels := by
      have hz : ∀ j, raw39817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39817step0 = (fun i j => raw39817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39817step0 raw39817; decide +kernel
      have hl : raw39817step0Labels = raw39817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39817 raw39817Labels permutation346 hz
    mixedMoment B raw39817step0 raw39817step0Labels = mixedMoment B raw39817step1 raw39817step1Labels := by
      have ha : raw39817step1 = (fun i j => raw39817step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39817step1 raw39817step0; decide +kernel
      have hl : raw39817step1Labels = raw39817step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39817step0 raw39817step0Labels permutation115 permutation6
    _ = mixedMoment B node384 node384Labels := by rfl

def raw39818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39818Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39818step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39818step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39818 raw39818Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw39818 raw39818Labels = mixedMoment B raw39818step0 raw39818step0Labels := by
      have hz : ∀ j, raw39818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39818step0 = (fun i j => raw39818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39818step0 raw39818; decide +kernel
      have hl : raw39818step0Labels = raw39818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39818 raw39818Labels permutation346 hz
    mixedMoment B raw39818step0 raw39818step0Labels = mixedMoment B raw39818step1 raw39818step1Labels := by
      have ha : raw39818step1 = (fun i j => raw39818step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39818step1 raw39818step0; decide +kernel
      have hl : raw39818step1Labels = raw39818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39818step0 raw39818step0Labels permutation149 permutation7
    _ = mixedMoment B node377 node377Labels := by rfl

def raw39819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw39819Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw39819step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39819step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39819 raw39819Labels = mixedMoment B node145 node145Labels := by
  calc
    mixedMoment B raw39819 raw39819Labels = mixedMoment B raw39819step0 raw39819step0Labels := by
      have hz : ∀ j, raw39819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39819step0 = (fun i j => raw39819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39819step0 raw39819; decide +kernel
      have hl : raw39819step0Labels = raw39819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39819 raw39819Labels permutation346 hz
    mixedMoment B raw39819step0 raw39819step0Labels = mixedMoment B raw39819step1 raw39819step1Labels := by
      have ha : raw39819step1 = (fun i j => raw39819step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39819step1 raw39819step0; decide +kernel
      have hl : raw39819step1Labels = raw39819step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39819step0 raw39819step0Labels permutation137 permutation6
    _ = mixedMoment B node145 node145Labels := by rfl

def raw39820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39820Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39820step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39820step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39820 raw39820Labels = mixedMoment B node139 node139Labels := by
  calc
    mixedMoment B raw39820 raw39820Labels = mixedMoment B raw39820step0 raw39820step0Labels := by
      have hz : ∀ j, raw39820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39820step0 = (fun i j => raw39820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39820step0 raw39820; decide +kernel
      have hl : raw39820step0Labels = raw39820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39820 raw39820Labels permutation346 hz
    mixedMoment B raw39820step0 raw39820step0Labels = mixedMoment B raw39820step1 raw39820step1Labels := by
      have ha : raw39820step1 = (fun i j => raw39820step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39820step1 raw39820step0; decide +kernel
      have hl : raw39820step1Labels = raw39820step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39820step0 raw39820step0Labels permutation138 permutation6
    _ = mixedMoment B node139 node139Labels := by rfl

def raw39821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39821Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39821step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39821 raw39821Labels = mixedMoment B node322 node322Labels := by
  calc
    mixedMoment B raw39821 raw39821Labels = mixedMoment B raw39821step0 raw39821step0Labels := by
      have ha : raw39821step0 = (fun i j => raw39821 (permutation492 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39821step0 raw39821; decide +kernel
      have hl : raw39821step0Labels = raw39821Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39821 raw39821Labels permutation492 permutation6
    _ = mixedMoment B node322 node322Labels := by rfl

def raw39822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39822Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39822step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39822 raw39822Labels = mixedMoment B node373 node373Labels := by
  calc
    mixedMoment B raw39822 raw39822Labels = mixedMoment B raw39822step0 raw39822step0Labels := by
      have ha : raw39822step0 = (fun i j => raw39822 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39822step0 raw39822; decide +kernel
      have hl : raw39822step0Labels = raw39822Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39822 raw39822Labels permutation463 permutation6
    _ = mixedMoment B node373 node373Labels := by rfl

def raw39823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39823Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw39823step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw39823step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw39823step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw39823step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39823 raw39823Labels = mixedMoment B node264 node264Labels := by
  calc
    mixedMoment B raw39823 raw39823Labels = mixedMoment B raw39823step0 raw39823step0Labels := by
      have hz : ∀ j, raw39823 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39823step0 = (fun i j => raw39823 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39823step0 raw39823; decide +kernel
      have hl : raw39823step0Labels = raw39823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39823 raw39823Labels permutation520 hz
    mixedMoment B raw39823step0 raw39823step0Labels = mixedMoment B raw39823step1 raw39823step1Labels := by
      have hz : ∀ j, raw39823step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39823step1 = (fun i j => raw39823step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39823step1 raw39823step0; decide +kernel
      have hl : raw39823step1Labels = raw39823step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39823step0 raw39823step0Labels permutation104 hz
    mixedMoment B raw39823step1 raw39823step1Labels = mixedMoment B raw39823step2 raw39823step2Labels := by
      have ha : raw39823step2 = (fun i j => raw39823step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39823step2 raw39823step1; decide +kernel
      have hl : raw39823step2Labels = raw39823step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39823step1 raw39823step1Labels permutation22 permutation4
    mixedMoment B raw39823step2 raw39823step2Labels = mixedMoment B raw39823step3 raw39823step3Labels := by
      have ha : raw39823step3 = -raw39823step2 := by apply Matrix.ext; change ∀ i j, raw39823step3 i j = -(raw39823step2 i j); unfold raw39823step3 raw39823step2; decide +kernel
      have hl : raw39823step3Labels = raw39823step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node264 node264Labels := by rfl

def raw39824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39824Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw39824step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39824step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39824step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39824 raw39824Labels = mixedMoment B node263 node263Labels := by
  calc
    mixedMoment B raw39824 raw39824Labels = mixedMoment B raw39824step0 raw39824step0Labels := by
      have hz : ∀ j, raw39824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39824step0 = (fun i j => raw39824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39824step0 raw39824; decide +kernel
      have hl : raw39824step0Labels = raw39824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39824 raw39824Labels permutation434 hz
    mixedMoment B raw39824step0 raw39824step0Labels = mixedMoment B raw39824step1 raw39824step1Labels := by
      have ha : raw39824step1 = (fun i j => raw39824step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39824step1 raw39824step0; decide +kernel
      have hl : raw39824step1Labels = raw39824step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39824step0 raw39824step0Labels permutation86 permutation4
    mixedMoment B raw39824step1 raw39824step1Labels = mixedMoment B raw39824step2 raw39824step2Labels := by
      have ha : raw39824step2 = -raw39824step1 := by apply Matrix.ext; change ∀ i j, raw39824step2 i j = -(raw39824step1 i j); unfold raw39824step2 raw39824step1; decide +kernel
      have hl : raw39824step2Labels = raw39824step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node263 node263Labels := by rfl

def raw39825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39825Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw39825step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39825step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39825 raw39825Labels = mixedMoment B node246 node246Labels := by
  calc
    mixedMoment B raw39825 raw39825Labels = mixedMoment B raw39825step0 raw39825step0Labels := by
      have hz : ∀ j, raw39825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39825step0 = (fun i j => raw39825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39825step0 raw39825; decide +kernel
      have hl : raw39825step0Labels = raw39825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39825 raw39825Labels permutation434 hz
    mixedMoment B raw39825step0 raw39825step0Labels = mixedMoment B raw39825step1 raw39825step1Labels := by
      have ha : raw39825step1 = (fun i j => raw39825step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39825step1 raw39825step0; decide +kernel
      have hl : raw39825step1Labels = raw39825step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39825step0 raw39825step0Labels permutation101 permutation6
    _ = mixedMoment B node246 node246Labels := by rfl

def raw39826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39826Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw39826step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw39826step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39826 raw39826Labels = mixedMoment B node177 node177Labels := by
  calc
    mixedMoment B raw39826 raw39826Labels = mixedMoment B raw39826step0 raw39826step0Labels := by
      have hz : ∀ j, raw39826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39826step0 = (fun i j => raw39826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39826step0 raw39826; decide +kernel
      have hl : raw39826step0Labels = raw39826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39826 raw39826Labels permutation434 hz
    mixedMoment B raw39826step0 raw39826step0Labels = mixedMoment B raw39826step1 raw39826step1Labels := by
      have ha : raw39826step1 = (fun i j => raw39826step0 (permutation100 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39826step1 raw39826step0; decide +kernel
      have hl : raw39826step1Labels = raw39826step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39826step0 raw39826step0Labels permutation100 permutation6
    _ = mixedMoment B node177 node177Labels := by rfl

def raw39827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39827Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39827step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39827 raw39827Labels = mixedMoment B node238 node238Labels := by
  calc
    mixedMoment B raw39827 raw39827Labels = mixedMoment B raw39827step0 raw39827step0Labels := by
      have ha : raw39827step0 = (fun i j => raw39827 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39827step0 raw39827; decide +kernel
      have hl : raw39827step0Labels = raw39827Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39827 raw39827Labels permutation431 permutation6
    _ = mixedMoment B node238 node238Labels := by rfl

def raw39828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39828Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39828step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39828 raw39828Labels = mixedMoment B node165 node165Labels := by
  calc
    mixedMoment B raw39828 raw39828Labels = mixedMoment B raw39828step0 raw39828step0Labels := by
      have ha : raw39828step0 = (fun i j => raw39828 (permutation430 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39828step0 raw39828; decide +kernel
      have hl : raw39828step0Labels = raw39828Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39828 raw39828Labels permutation430 permutation6
    _ = mixedMoment B node165 node165Labels := by rfl

def raw39829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39829Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw39829step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39829step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39829step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39829 raw39829Labels = mixedMoment B node263 node263Labels := by
  calc
    mixedMoment B raw39829 raw39829Labels = mixedMoment B raw39829step0 raw39829step0Labels := by
      have hz : ∀ j, raw39829 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39829step0 = (fun i j => raw39829 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39829step0 raw39829; decide +kernel
      have hl : raw39829step0Labels = raw39829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39829 raw39829Labels permutation520 hz
    mixedMoment B raw39829step0 raw39829step0Labels = mixedMoment B raw39829step1 raw39829step1Labels := by
      have ha : raw39829step1 = (fun i j => raw39829step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39829step1 raw39829step0; decide +kernel
      have hl : raw39829step1Labels = raw39829step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39829step0 raw39829step0Labels permutation151 permutation3
    mixedMoment B raw39829step1 raw39829step1Labels = mixedMoment B raw39829step2 raw39829step2Labels := by
      have ha : raw39829step2 = -raw39829step1 := by apply Matrix.ext; change ∀ i j, raw39829step2 i j = -(raw39829step1 i j); unfold raw39829step2 raw39829step1; decide +kernel
      have hl : raw39829step2Labels = raw39829step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node263 node263Labels := by rfl

def raw39830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39830Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39830step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39830 raw39830Labels = mixedMoment B node463 node463Labels := by
  calc
    mixedMoment B raw39830 raw39830Labels = mixedMoment B raw39830step0 raw39830step0Labels := by
      have ha : raw39830step0 = (fun i j => raw39830 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39830step0 raw39830; decide +kernel
      have hl : raw39830step0Labels = raw39830Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39830 raw39830Labels permutation158 permutation2
    _ = mixedMoment B node463 node463Labels := by rfl

def raw39831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39831Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39831step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39831 raw39831Labels = mixedMoment B node458 node458Labels := by
  calc
    mixedMoment B raw39831 raw39831Labels = mixedMoment B raw39831step0 raw39831step0Labels := by
      have ha : raw39831step0 = (fun i j => raw39831 (permutation397 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39831step0 raw39831; decide +kernel
      have hl : raw39831step0Labels = raw39831Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39831 raw39831Labels permutation397 permutation6
    _ = mixedMoment B node458 node458Labels := by rfl

def raw39832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39832Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw39832step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39832 raw39832Labels = mixedMoment B node356 node356Labels := by
  calc
    mixedMoment B raw39832 raw39832Labels = mixedMoment B raw39832step0 raw39832step0Labels := by
      have ha : raw39832step0 = (fun i j => raw39832 (permutation525 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39832step0 raw39832; decide +kernel
      have hl : raw39832step0Labels = raw39832Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39832 raw39832Labels permutation525 permutation4
    _ = mixedMoment B node356 node356Labels := by rfl

def raw39833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39833Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw39833step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw39833step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39833 raw39833Labels = mixedMoment B node398 node398Labels := by
  calc
    mixedMoment B raw39833 raw39833Labels = mixedMoment B raw39833step0 raw39833step0Labels := by
      have hz : ∀ j, raw39833 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39833step0 = (fun i j => raw39833 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39833step0 raw39833; decide +kernel
      have hl : raw39833step0Labels = raw39833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39833 raw39833Labels permutation434 hz
    mixedMoment B raw39833step0 raw39833step0Labels = mixedMoment B raw39833step1 raw39833step1Labels := by
      have ha : raw39833step1 = (fun i j => raw39833step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39833step1 raw39833step0; decide +kernel
      have hl : raw39833step1Labels = raw39833step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39833step0 raw39833step0Labels permutation135 permutation5
    _ = mixedMoment B node398 node398Labels := by rfl

def raw39834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39834Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39834step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39834step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39834step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39834 raw39834Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39834 raw39834Labels = mixedMoment B raw39834step0 raw39834step0Labels := by
      have hz : ∀ j, raw39834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39834step0 = (fun i j => raw39834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39834step0 raw39834; decide +kernel
      have hl : raw39834step0Labels = raw39834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39834 raw39834Labels permutation434 hz
    mixedMoment B raw39834step0 raw39834step0Labels = mixedMoment B raw39834step1 raw39834step1Labels := by
      have ha : raw39834step1 = (fun i j => raw39834step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39834step1 raw39834step0; decide +kernel
      have hl : raw39834step1Labels = raw39834step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39834step0 raw39834step0Labels permutation35 permutation7
    mixedMoment B raw39834step1 raw39834step1Labels = mixedMoment B raw39834step2 raw39834step2Labels := by
      have ha : raw39834step2 = -raw39834step1 := by apply Matrix.ext; change ∀ i j, raw39834step2 i j = -(raw39834step1 i j); unfold raw39834step2 raw39834step1; decide +kernel
      have hl : raw39834step2Labels = raw39834step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node467 node467Labels := by rfl

def raw39835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39835Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39835step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39835step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39835 raw39835Labels = mixedMoment B node446 node446Labels := by
  calc
    mixedMoment B raw39835 raw39835Labels = mixedMoment B raw39835step0 raw39835step0Labels := by
      have hz : ∀ j, raw39835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39835step0 = (fun i j => raw39835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39835step0 raw39835; decide +kernel
      have hl : raw39835step0Labels = raw39835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39835 raw39835Labels permutation434 hz
    mixedMoment B raw39835step0 raw39835step0Labels = mixedMoment B raw39835step1 raw39835step1Labels := by
      have ha : raw39835step1 = (fun i j => raw39835step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39835step1 raw39835step0; decide +kernel
      have hl : raw39835step1Labels = raw39835step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39835step0 raw39835step0Labels permutation145 permutation7
    _ = mixedMoment B node446 node446Labels := by rfl

def raw39836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39836Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw39836step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39836step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39836 raw39836Labels = mixedMoment B node288 node288Labels := by
  calc
    mixedMoment B raw39836 raw39836Labels = mixedMoment B raw39836step0 raw39836step0Labels := by
      have hz : ∀ j, raw39836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39836step0 = (fun i j => raw39836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39836step0 raw39836; decide +kernel
      have hl : raw39836step0Labels = raw39836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39836 raw39836Labels permutation434 hz
    mixedMoment B raw39836step0 raw39836step0Labels = mixedMoment B raw39836step1 raw39836step1Labels := by
      have ha : raw39836step1 = (fun i j => raw39836step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39836step1 raw39836step0; decide +kernel
      have hl : raw39836step1Labels = raw39836step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39836step0 raw39836step0Labels permutation143 permutation7
    _ = mixedMoment B node288 node288Labels := by rfl

def raw39837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39837Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39837step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39837 raw39837Labels = mixedMoment B node434 node434Labels := by
  calc
    mixedMoment B raw39837 raw39837Labels = mixedMoment B raw39837step0 raw39837step0Labels := by
      have ha : raw39837step0 = (fun i j => raw39837 (permutation412 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39837step0 raw39837; decide +kernel
      have hl : raw39837step0Labels = raw39837Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39837 raw39837Labels permutation412 permutation6
    _ = mixedMoment B node434 node434Labels := by rfl

def raw39838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39838Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39838step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39838 raw39838Labels = mixedMoment B node280 node280Labels := by
  calc
    mixedMoment B raw39838 raw39838Labels = mixedMoment B raw39838step0 raw39838step0Labels := by
      have ha : raw39838step0 = (fun i j => raw39838 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39838step0 raw39838; decide +kernel
      have hl : raw39838step0Labels = raw39838Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39838 raw39838Labels permutation646 permutation7
    _ = mixedMoment B node280 node280Labels := by rfl

def raw39839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39839Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39839step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39839 raw39839Labels = mixedMoment B node278 node278Labels := by
  calc
    mixedMoment B raw39839 raw39839Labels = mixedMoment B raw39839step0 raw39839step0Labels := by
      have ha : raw39839step0 = (fun i j => raw39839 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39839step0 raw39839; decide +kernel
      have hl : raw39839step0Labels = raw39839Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39839 raw39839Labels permutation644 permutation7
    _ = mixedMoment B node278 node278Labels := by rfl

def raw39840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39840Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw39840step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39840step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39840 raw39840Labels = mixedMoment B node313 node313Labels := by
  calc
    mixedMoment B raw39840 raw39840Labels = mixedMoment B raw39840step0 raw39840step0Labels := by
      have hz : ∀ j, raw39840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39840step0 = (fun i j => raw39840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39840step0 raw39840; decide +kernel
      have hl : raw39840step0Labels = raw39840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39840 raw39840Labels permutation434 hz
    mixedMoment B raw39840step0 raw39840step0Labels = mixedMoment B raw39840step1 raw39840step1Labels := by
      have ha : raw39840step1 = (fun i j => raw39840step0 (permutation119 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39840step1 raw39840step0; decide +kernel
      have hl : raw39840step1Labels = raw39840step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39840step0 raw39840step0Labels permutation119 permutation6
    _ = mixedMoment B node313 node313Labels := by rfl

def raw39841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39841Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw39841step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw39841step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39841 raw39841Labels = mixedMoment B node123 node123Labels := by
  calc
    mixedMoment B raw39841 raw39841Labels = mixedMoment B raw39841step0 raw39841step0Labels := by
      have hz : ∀ j, raw39841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39841step0 = (fun i j => raw39841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39841step0 raw39841; decide +kernel
      have hl : raw39841step0Labels = raw39841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39841 raw39841Labels permutation434 hz
    mixedMoment B raw39841step0 raw39841step0Labels = mixedMoment B raw39841step1 raw39841step1Labels := by
      have ha : raw39841step1 = (fun i j => raw39841step0 (permutation142 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39841step1 raw39841step0; decide +kernel
      have hl : raw39841step1Labels = raw39841step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39841step0 raw39841step0Labels permutation142 permutation6
    _ = mixedMoment B node123 node123Labels := by rfl

def raw39842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39842Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39842step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39842 raw39842Labels = mixedMoment B node5508 node5508Labels := by
  calc
    mixedMoment B raw39842 raw39842Labels = mixedMoment B raw39842step0 raw39842step0Labels := by
      have ha : raw39842step0 = (fun i j => raw39842 (permutation550 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39842step0 raw39842; decide +kernel
      have hl : raw39842step0Labels = raw39842Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39842 raw39842Labels permutation550 permutation6
    _ = mixedMoment B node5508 node5508Labels := by rfl

def raw39843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39843Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39843step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39843 raw39843Labels = mixedMoment B node114 node114Labels := by
  calc
    mixedMoment B raw39843 raw39843Labels = mixedMoment B raw39843step0 raw39843step0Labels := by
      have ha : raw39843step0 = (fun i j => raw39843 (permutation643 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39843step0 raw39843; decide +kernel
      have hl : raw39843step0Labels = raw39843Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39843 raw39843Labels permutation643 permutation6
    _ = mixedMoment B node114 node114Labels := by rfl

def raw39844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39844Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39844step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -3, 2], ![2, 3, -5]]
def raw39844step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw39844step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39844 raw39844Labels = mixedMoment B node29 node29Labels := by
  calc
    mixedMoment B raw39844 raw39844Labels = mixedMoment B raw39844step0 raw39844step0Labels := by
      have hz : ∀ j, raw39844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39844step0 = (fun i j => raw39844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39844step0 raw39844; decide +kernel
      have hl : raw39844step0Labels = raw39844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39844 raw39844Labels permutation434 hz
    mixedMoment B raw39844step0 raw39844step0Labels = mixedMoment B raw39844step1 raw39844step1Labels := by
      have hz : ∀ j, raw39844step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39844step1 = (fun i j => raw39844step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39844step1 raw39844step0; decide +kernel
      have hl : raw39844step1Labels = raw39844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39844step0 raw39844step0Labels permutation80 hz
    mixedMoment B raw39844step1 raw39844step1Labels = mixedMoment B raw39844step2 raw39844step2Labels := by
      have ha : raw39844step2 = (fun i j => raw39844step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39844step2 raw39844step1; decide +kernel
      have hl : raw39844step2Labels = raw39844step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39844step1 raw39844step1Labels permutation28 permutation6
    _ = mixedMoment B node29 node29Labels := by rfl

def raw39845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39845Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39845step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39845step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39845 raw39845Labels = mixedMoment B node101 node101Labels := by
  calc
    mixedMoment B raw39845 raw39845Labels = mixedMoment B raw39845step0 raw39845step0Labels := by
      have hz : ∀ j, raw39845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39845step0 = (fun i j => raw39845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39845step0 raw39845; decide +kernel
      have hl : raw39845step0Labels = raw39845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39845 raw39845Labels permutation346 hz
    mixedMoment B raw39845step0 raw39845step0Labels = mixedMoment B raw39845step1 raw39845step1Labels := by
      have ha : raw39845step1 = (fun i j => raw39845step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39845step1 raw39845step0; decide +kernel
      have hl : raw39845step1Labels = raw39845step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39845step0 raw39845step0Labels permutation125 permutation6
    _ = mixedMoment B node101 node101Labels := by rfl

def raw39846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39846Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39846step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39846step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39846 raw39846Labels = mixedMoment B node142 node142Labels := by
  calc
    mixedMoment B raw39846 raw39846Labels = mixedMoment B raw39846step0 raw39846step0Labels := by
      have hz : ∀ j, raw39846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39846step0 = (fun i j => raw39846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39846step0 raw39846; decide +kernel
      have hl : raw39846step0Labels = raw39846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39846 raw39846Labels permutation346 hz
    mixedMoment B raw39846step0 raw39846step0Labels = mixedMoment B raw39846step1 raw39846step1Labels := by
      have ha : raw39846step1 = (fun i j => raw39846step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39846step1 raw39846step0; decide +kernel
      have hl : raw39846step1Labels = raw39846step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39846step0 raw39846step0Labels permutation151 permutation7
    _ = mixedMoment B node142 node142Labels := by rfl

def raw39847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39847Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39847step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39847step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39847 raw39847Labels = mixedMoment B node27 node27Labels := by
  calc
    mixedMoment B raw39847 raw39847Labels = mixedMoment B raw39847step0 raw39847step0Labels := by
      have hz : ∀ j, raw39847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39847step0 = (fun i j => raw39847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39847step0 raw39847; decide +kernel
      have hl : raw39847step0Labels = raw39847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39847 raw39847Labels permutation346 hz
    mixedMoment B raw39847step0 raw39847step0Labels = mixedMoment B raw39847step1 raw39847step1Labels := by
      have ha : raw39847step1 = (fun i j => raw39847step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39847step1 raw39847step0; decide +kernel
      have hl : raw39847step1Labels = raw39847step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39847step0 raw39847step0Labels permutation137 permutation6
    _ = mixedMoment B node27 node27Labels := by rfl

def raw39848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39848Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39848step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39848step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39848 raw39848Labels = mixedMoment B node12 node12Labels := by
  calc
    mixedMoment B raw39848 raw39848Labels = mixedMoment B raw39848step0 raw39848step0Labels := by
      have hz : ∀ j, raw39848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39848step0 = (fun i j => raw39848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39848step0 raw39848; decide +kernel
      have hl : raw39848step0Labels = raw39848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39848 raw39848Labels permutation346 hz
    mixedMoment B raw39848step0 raw39848step0Labels = mixedMoment B raw39848step1 raw39848step1Labels := by
      have ha : raw39848step1 = (fun i j => raw39848step0 (permutation148 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39848step1 raw39848step0; decide +kernel
      have hl : raw39848step1Labels = raw39848step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39848step0 raw39848step0Labels permutation148 permutation6
    _ = mixedMoment B node12 node12Labels := by rfl

def raw39849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39849Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39849step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39849 raw39849Labels = mixedMoment B node10 node10Labels := by
  calc
    mixedMoment B raw39849 raw39849Labels = mixedMoment B raw39849step0 raw39849step0Labels := by
      have ha : raw39849step0 = (fun i j => raw39849 (permutation674 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39849step0 raw39849; decide +kernel
      have hl : raw39849step0Labels = raw39849Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39849 raw39849Labels permutation674 permutation6
    _ = mixedMoment B node10 node10Labels := by rfl

def raw39850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39850Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw39850step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39850step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39850 raw39850Labels = mixedMoment B node229 node229Labels := by
  calc
    mixedMoment B raw39850 raw39850Labels = mixedMoment B raw39850step0 raw39850step0Labels := by
      have hz : ∀ j, raw39850 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39850step0 = (fun i j => raw39850 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39850step0 raw39850; decide +kernel
      have hl : raw39850step0Labels = raw39850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39850 raw39850Labels permutation434 hz
    mixedMoment B raw39850step0 raw39850step0Labels = mixedMoment B raw39850step1 raw39850step1Labels := by
      have ha : raw39850step1 = (fun i j => raw39850step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39850step1 raw39850step0; decide +kernel
      have hl : raw39850step1Labels = raw39850step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39850step0 raw39850step0Labels permutation96 permutation6
    _ = mixedMoment B node229 node229Labels := by rfl

def raw39851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39851Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw39851step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39851step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39851 raw39851Labels = mixedMoment B node240 node240Labels := by
  calc
    mixedMoment B raw39851 raw39851Labels = mixedMoment B raw39851step0 raw39851step0Labels := by
      have hz : ∀ j, raw39851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39851step0 = (fun i j => raw39851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39851step0 raw39851; decide +kernel
      have hl : raw39851step0Labels = raw39851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39851 raw39851Labels permutation434 hz
    mixedMoment B raw39851step0 raw39851step0Labels = mixedMoment B raw39851step1 raw39851step1Labels := by
      have ha : raw39851step1 = (fun i j => raw39851step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39851step1 raw39851step0; decide +kernel
      have hl : raw39851step1Labels = raw39851step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39851step0 raw39851step0Labels permutation102 permutation6
    _ = mixedMoment B node240 node240Labels := by rfl

def raw39852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39852Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw39852step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39852step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39852 raw39852Labels = mixedMoment B node184 node184Labels := by
  calc
    mixedMoment B raw39852 raw39852Labels = mixedMoment B raw39852step0 raw39852step0Labels := by
      have hz : ∀ j, raw39852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39852step0 = (fun i j => raw39852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39852step0 raw39852; decide +kernel
      have hl : raw39852step0Labels = raw39852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39852 raw39852Labels permutation434 hz
    mixedMoment B raw39852step0 raw39852step0Labels = mixedMoment B raw39852step1 raw39852step1Labels := by
      have ha : raw39852step1 = (fun i j => raw39852step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39852step1 raw39852step0; decide +kernel
      have hl : raw39852step1Labels = raw39852step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39852step0 raw39852step0Labels permutation102 permutation6
    _ = mixedMoment B node184 node184Labels := by rfl

def raw39853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39853Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39853step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39853 raw39853Labels = mixedMoment B node167 node167Labels := by
  calc
    mixedMoment B raw39853 raw39853Labels = mixedMoment B raw39853step0 raw39853step0Labels := by
      have ha : raw39853step0 = (fun i j => raw39853 (permutation432 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39853step0 raw39853; decide +kernel
      have hl : raw39853step0Labels = raw39853Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39853 raw39853Labels permutation432 permutation6
    _ = mixedMoment B node167 node167Labels := by rfl

def raw39854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39854Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39854step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39854step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39854 raw39854Labels = mixedMoment B node434 node434Labels := by
  calc
    mixedMoment B raw39854 raw39854Labels = mixedMoment B raw39854step0 raw39854step0Labels := by
      have ha : raw39854step0 = (fun i j => raw39854 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39854step0 raw39854; decide +kernel
      have hl : raw39854step0Labels = raw39854Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39854 raw39854Labels permutation173 permutation7
    mixedMoment B raw39854step0 raw39854step0Labels = mixedMoment B raw39854step1 raw39854step1Labels := by
      have ha : raw39854step1 = -raw39854step0 := by apply Matrix.ext; change ∀ i j, raw39854step1 i j = -(raw39854step0 i j); unfold raw39854step1 raw39854step0; decide +kernel
      have hl : raw39854step1Labels = raw39854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node434 node434Labels := by rfl

def raw39855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39855Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39855step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39855step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39855 raw39855Labels = mixedMoment B node427 node427Labels := by
  calc
    mixedMoment B raw39855 raw39855Labels = mixedMoment B raw39855step0 raw39855step0Labels := by
      have ha : raw39855step0 = (fun i j => raw39855 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39855step0 raw39855; decide +kernel
      have hl : raw39855step0Labels = raw39855Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39855 raw39855Labels permutation166 permutation7
    mixedMoment B raw39855step0 raw39855step0Labels = mixedMoment B raw39855step1 raw39855step1Labels := by
      have ha : raw39855step1 = -raw39855step0 := by apply Matrix.ext; change ∀ i j, raw39855step1 i j = -(raw39855step0 i j); unfold raw39855step1 raw39855step0; decide +kernel
      have hl : raw39855step1Labels = raw39855step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node427 node427Labels := by rfl

def raw39856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39856Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39856step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39856step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39856 raw39856Labels = mixedMoment B node435 node435Labels := by
  calc
    mixedMoment B raw39856 raw39856Labels = mixedMoment B raw39856step0 raw39856step0Labels := by
      have hz : ∀ j, raw39856 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39856step0 = (fun i j => raw39856 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39856step0 raw39856; decide +kernel
      have hl : raw39856step0Labels = raw39856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39856 raw39856Labels permutation434 hz
    mixedMoment B raw39856step0 raw39856step0Labels = mixedMoment B raw39856step1 raw39856step1Labels := by
      have ha : raw39856step1 = (fun i j => raw39856step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39856step1 raw39856step0; decide +kernel
      have hl : raw39856step1Labels = raw39856step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39856step0 raw39856step0Labels permutation96 permutation6
    _ = mixedMoment B node435 node435Labels := by rfl

def raw39857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39857Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39857step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39857step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39857step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39857 raw39857Labels = mixedMoment B node432 node432Labels := by
  calc
    mixedMoment B raw39857 raw39857Labels = mixedMoment B raw39857step0 raw39857step0Labels := by
      have hz : ∀ j, raw39857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39857step0 = (fun i j => raw39857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39857step0 raw39857; decide +kernel
      have hl : raw39857step0Labels = raw39857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39857 raw39857Labels permutation434 hz
    mixedMoment B raw39857step0 raw39857step0Labels = mixedMoment B raw39857step1 raw39857step1Labels := by
      have ha : raw39857step1 = (fun i j => raw39857step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39857step1 raw39857step0; decide +kernel
      have hl : raw39857step1Labels = raw39857step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39857step0 raw39857step0Labels permutation34 permutation7
    mixedMoment B raw39857step1 raw39857step1Labels = mixedMoment B raw39857step2 raw39857step2Labels := by
      have ha : raw39857step2 = -raw39857step1 := by apply Matrix.ext; change ∀ i j, raw39857step2 i j = -(raw39857step1 i j); unfold raw39857step2 raw39857step1; decide +kernel
      have hl : raw39857step2Labels = raw39857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node432 node432Labels := by rfl

def raw39858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39858Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw39858step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39858step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39858 raw39858Labels = mixedMoment B node282 node282Labels := by
  calc
    mixedMoment B raw39858 raw39858Labels = mixedMoment B raw39858step0 raw39858step0Labels := by
      have hz : ∀ j, raw39858 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39858step0 = (fun i j => raw39858 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39858step0 raw39858; decide +kernel
      have hl : raw39858step0Labels = raw39858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39858 raw39858Labels permutation434 hz
    mixedMoment B raw39858step0 raw39858step0Labels = mixedMoment B raw39858step1 raw39858step1Labels := by
      have ha : raw39858step1 = (fun i j => raw39858step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39858step1 raw39858step0; decide +kernel
      have hl : raw39858step1Labels = raw39858step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39858step0 raw39858step0Labels permutation145 permutation7
    _ = mixedMoment B node282 node282Labels := by rfl

def raw39859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39859Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39859step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39859 raw39859Labels = mixedMoment B node426 node426Labels := by
  calc
    mixedMoment B raw39859 raw39859Labels = mixedMoment B raw39859step0 raw39859step0Labels := by
      have ha : raw39859step0 = (fun i j => raw39859 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39859step0 raw39859; decide +kernel
      have hl : raw39859step0Labels = raw39859Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39859 raw39859Labels permutation393 permutation6
    _ = mixedMoment B node426 node426Labels := by rfl

def raw39860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39860Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39860step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39860 raw39860Labels = mixedMoment B node428 node428Labels := by
  calc
    mixedMoment B raw39860 raw39860Labels = mixedMoment B raw39860step0 raw39860step0Labels := by
      have ha : raw39860step0 = (fun i j => raw39860 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39860step0 raw39860; decide +kernel
      have hl : raw39860step0Labels = raw39860Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39860 raw39860Labels permutation393 permutation6
    _ = mixedMoment B node428 node428Labels := by rfl

def raw39861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39861Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39861step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39861step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39861 raw39861Labels = mixedMoment B node429 node429Labels := by
  calc
    mixedMoment B raw39861 raw39861Labels = mixedMoment B raw39861step0 raw39861step0Labels := by
      have ha : raw39861step0 = (fun i j => raw39861 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39861step0 raw39861; decide +kernel
      have hl : raw39861step0Labels = raw39861Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39861 raw39861Labels permutation164 permutation7
    mixedMoment B raw39861step0 raw39861step0Labels = mixedMoment B raw39861step1 raw39861step1Labels := by
      have ha : raw39861step1 = -raw39861step0 := by apply Matrix.ext; change ∀ i j, raw39861step1 i j = -(raw39861step0 i j); unfold raw39861step1 raw39861step0; decide +kernel
      have hl : raw39861step1Labels = raw39861step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node429 node429Labels := by rfl

def raw39862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39862Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw39862step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39862step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39862 raw39862Labels = mixedMoment B node309 node309Labels := by
  calc
    mixedMoment B raw39862 raw39862Labels = mixedMoment B raw39862step0 raw39862step0Labels := by
      have hz : ∀ j, raw39862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39862step0 = (fun i j => raw39862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39862step0 raw39862; decide +kernel
      have hl : raw39862step0Labels = raw39862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39862 raw39862Labels permutation434 hz
    mixedMoment B raw39862step0 raw39862step0Labels = mixedMoment B raw39862step1 raw39862step1Labels := by
      have ha : raw39862step1 = (fun i j => raw39862step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39862step1 raw39862step0; decide +kernel
      have hl : raw39862step1Labels = raw39862step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39862step0 raw39862step0Labels permutation120 permutation6
    _ = mixedMoment B node309 node309Labels := by rfl

def raw39863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39863Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39863step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39863step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39863 raw39863Labels = mixedMoment B node325 node325Labels := by
  calc
    mixedMoment B raw39863 raw39863Labels = mixedMoment B raw39863step0 raw39863step0Labels := by
      have hz : ∀ j, raw39863 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39863step0 = (fun i j => raw39863 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39863step0 raw39863; decide +kernel
      have hl : raw39863step0Labels = raw39863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39863 raw39863Labels permutation434 hz
    mixedMoment B raw39863step0 raw39863step0Labels = mixedMoment B raw39863step1 raw39863step1Labels := by
      have ha : raw39863step1 = (fun i j => raw39863step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39863step1 raw39863step0; decide +kernel
      have hl : raw39863step1Labels = raw39863step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39863step0 raw39863step0Labels permutation145 permutation7
    _ = mixedMoment B node325 node325Labels := by rfl

def raw39864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39864Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw39864step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39864step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39864 raw39864Labels = mixedMoment B node130 node130Labels := by
  calc
    mixedMoment B raw39864 raw39864Labels = mixedMoment B raw39864step0 raw39864step0Labels := by
      have hz : ∀ j, raw39864 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39864step0 = (fun i j => raw39864 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39864step0 raw39864; decide +kernel
      have hl : raw39864step0Labels = raw39864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39864 raw39864Labels permutation434 hz
    mixedMoment B raw39864step0 raw39864step0Labels = mixedMoment B raw39864step1 raw39864step1Labels := by
      have ha : raw39864step1 = (fun i j => raw39864step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39864step1 raw39864step0; decide +kernel
      have hl : raw39864step1Labels = raw39864step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39864step0 raw39864step0Labels permutation144 permutation6
    _ = mixedMoment B node130 node130Labels := by rfl

def raw39865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39865Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39865step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39865 raw39865Labels = mixedMoment B node296 node296Labels := by
  calc
    mixedMoment B raw39865 raw39865Labels = mixedMoment B raw39865step0 raw39865step0Labels := by
      have ha : raw39865step0 = (fun i j => raw39865 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39865step0 raw39865; decide +kernel
      have hl : raw39865step0Labels = raw39865Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39865 raw39865Labels permutation479 permutation6
    _ = mixedMoment B node296 node296Labels := by rfl

def raw39866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39866Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39866step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39866 raw39866Labels = mixedMoment B node300 node300Labels := by
  calc
    mixedMoment B raw39866 raw39866Labels = mixedMoment B raw39866step0 raw39866step0Labels := by
      have ha : raw39866step0 = (fun i j => raw39866 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39866step0 raw39866; decide +kernel
      have hl : raw39866step0Labels = raw39866Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39866 raw39866Labels permutation479 permutation6
    _ = mixedMoment B node300 node300Labels := by rfl

def raw39867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39867Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39867step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw39867step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39867step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39867 raw39867Labels = mixedMoment B node103 node103Labels := by
  calc
    mixedMoment B raw39867 raw39867Labels = mixedMoment B raw39867step0 raw39867step0Labels := by
      have hz : ∀ j, raw39867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39867step0 = (fun i j => raw39867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39867step0 raw39867; decide +kernel
      have hl : raw39867step0Labels = raw39867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39867 raw39867Labels permutation434 hz
    mixedMoment B raw39867step0 raw39867step0Labels = mixedMoment B raw39867step1 raw39867step1Labels := by
      have hz : ∀ j, raw39867step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39867step1 = (fun i j => raw39867step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39867step1 raw39867step0; decide +kernel
      have hl : raw39867step1Labels = raw39867step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39867step0 raw39867step0Labels permutation80 hz
    mixedMoment B raw39867step1 raw39867step1Labels = mixedMoment B raw39867step2 raw39867step2Labels := by
      have ha : raw39867step2 = (fun i j => raw39867step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39867step2 raw39867step1; decide +kernel
      have hl : raw39867step2Labels = raw39867step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39867step1 raw39867step1Labels permutation24 permutation6
    _ = mixedMoment B node103 node103Labels := by rfl

def raw39868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39868Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39868step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39868step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39868step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39868 raw39868Labels = mixedMoment B node149 node149Labels := by
  calc
    mixedMoment B raw39868 raw39868Labels = mixedMoment B raw39868step0 raw39868step0Labels := by
      have hz : ∀ j, raw39868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39868step0 = (fun i j => raw39868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39868step0 raw39868; decide +kernel
      have hl : raw39868step0Labels = raw39868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39868 raw39868Labels permutation434 hz
    mixedMoment B raw39868step0 raw39868step0Labels = mixedMoment B raw39868step1 raw39868step1Labels := by
      have hz : ∀ j, raw39868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39868step1 = (fun i j => raw39868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39868step1 raw39868step0; decide +kernel
      have hl : raw39868step1Labels = raw39868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39868step0 raw39868step0Labels permutation80 hz
    mixedMoment B raw39868step1 raw39868step1Labels = mixedMoment B raw39868step2 raw39868step2Labels := by
      have ha : raw39868step2 = (fun i j => raw39868step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39868step2 raw39868step1; decide +kernel
      have hl : raw39868step2Labels = raw39868step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39868step1 raw39868step1Labels permutation31 permutation7
    _ = mixedMoment B node149 node149Labels := by rfl

def raw39869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39869Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39869step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw39869step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39869step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39869 raw39869Labels = mixedMoment B node36 node36Labels := by
  calc
    mixedMoment B raw39869 raw39869Labels = mixedMoment B raw39869step0 raw39869step0Labels := by
      have hz : ∀ j, raw39869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39869step0 = (fun i j => raw39869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39869step0 raw39869; decide +kernel
      have hl : raw39869step0Labels = raw39869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39869 raw39869Labels permutation434 hz
    mixedMoment B raw39869step0 raw39869step0Labels = mixedMoment B raw39869step1 raw39869step1Labels := by
      have hz : ∀ j, raw39869step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39869step1 = (fun i j => raw39869step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39869step1 raw39869step0; decide +kernel
      have hl : raw39869step1Labels = raw39869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39869step0 raw39869step0Labels permutation80 hz
    mixedMoment B raw39869step1 raw39869step1Labels = mixedMoment B raw39869step2 raw39869step2Labels := by
      have ha : raw39869step2 = (fun i j => raw39869step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39869step2 raw39869step1; decide +kernel
      have hl : raw39869step2Labels = raw39869step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39869step1 raw39869step1Labels permutation30 permutation6
    _ = mixedMoment B node36 node36Labels := by rfl

def raw39870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39870Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39870step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39870step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39870 raw39870Labels = mixedMoment B node15 node15Labels := by
  calc
    mixedMoment B raw39870 raw39870Labels = mixedMoment B raw39870step0 raw39870step0Labels := by
      have hz : ∀ j, raw39870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39870step0 = (fun i j => raw39870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39870step0 raw39870; decide +kernel
      have hl : raw39870step0Labels = raw39870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39870 raw39870Labels permutation346 hz
    mixedMoment B raw39870step0 raw39870step0Labels = mixedMoment B raw39870step1 raw39870step1Labels := by
      have ha : raw39870step1 = (fun i j => raw39870step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39870step1 raw39870step0; decide +kernel
      have hl : raw39870step1Labels = raw39870step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39870step0 raw39870step0Labels permutation150 permutation6
    _ = mixedMoment B node15 node15Labels := by rfl

def raw39871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39871Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw39871step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39871step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39871 raw39871Labels = mixedMoment B node168 node168Labels := by
  calc
    mixedMoment B raw39871 raw39871Labels = mixedMoment B raw39871step0 raw39871step0Labels := by
      have hz : ∀ j, raw39871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39871step0 = (fun i j => raw39871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39871step0 raw39871; decide +kernel
      have hl : raw39871step0Labels = raw39871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39871 raw39871Labels permutation434 hz
    mixedMoment B raw39871step0 raw39871step0Labels = mixedMoment B raw39871step1 raw39871step1Labels := by
      have ha : raw39871step1 = (fun i j => raw39871step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39871step1 raw39871step0; decide +kernel
      have hl : raw39871step1Labels = raw39871step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39871step0 raw39871step0Labels permutation102 permutation6
    _ = mixedMoment B node168 node168Labels := by rfl

def raw39872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39872Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39872step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39872step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39872 raw39872Labels = mixedMoment B node278 node278Labels := by
  calc
    mixedMoment B raw39872 raw39872Labels = mixedMoment B raw39872step0 raw39872step0Labels := by
      have ha : raw39872step0 = (fun i j => raw39872 (permutation280 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39872step0 raw39872; decide +kernel
      have hl : raw39872step0Labels = raw39872Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39872 raw39872Labels permutation280 permutation6
    mixedMoment B raw39872step0 raw39872step0Labels = mixedMoment B raw39872step1 raw39872step1Labels := by
      have ha : raw39872step1 = -raw39872step0 := by apply Matrix.ext; change ∀ i j, raw39872step1 i j = -(raw39872step0 i j); unfold raw39872step1 raw39872step0; decide +kernel
      have hl : raw39872step1Labels = raw39872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node278 node278Labels := by rfl

def raw39873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39873Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw39873step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw39873step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw39873step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39873 raw39873Labels = mixedMoment B node279 node279Labels := by
  calc
    mixedMoment B raw39873 raw39873Labels = mixedMoment B raw39873step0 raw39873step0Labels := by
      have hz : ∀ j, raw39873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39873step0 = (fun i j => raw39873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39873step0 raw39873; decide +kernel
      have hl : raw39873step0Labels = raw39873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39873 raw39873Labels permutation434 hz
    mixedMoment B raw39873step0 raw39873step0Labels = mixedMoment B raw39873step1 raw39873step1Labels := by
      have ha : raw39873step1 = (fun i j => raw39873step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39873step1 raw39873step0; decide +kernel
      have hl : raw39873step1Labels = raw39873step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39873step0 raw39873step0Labels permutation58 permutation6
    mixedMoment B raw39873step1 raw39873step1Labels = mixedMoment B raw39873step2 raw39873step2Labels := by
      have ha : raw39873step2 = -raw39873step1 := by apply Matrix.ext; change ∀ i j, raw39873step2 i j = -(raw39873step1 i j); unfold raw39873step2 raw39873step1; decide +kernel
      have hl : raw39873step2Labels = raw39873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node279 node279Labels := by rfl

def raw39874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39874Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw39874step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39874step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39874 raw39874Labels = mixedMoment B node116 node116Labels := by
  calc
    mixedMoment B raw39874 raw39874Labels = mixedMoment B raw39874step0 raw39874step0Labels := by
      have hz : ∀ j, raw39874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39874step0 = (fun i j => raw39874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39874step0 raw39874; decide +kernel
      have hl : raw39874step0Labels = raw39874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39874 raw39874Labels permutation434 hz
    mixedMoment B raw39874step0 raw39874step0Labels = mixedMoment B raw39874step1 raw39874step1Labels := by
      have ha : raw39874step1 = (fun i j => raw39874step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39874step1 raw39874step0; decide +kernel
      have hl : raw39874step1Labels = raw39874step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39874step0 raw39874step0Labels permutation144 permutation6
    _ = mixedMoment B node116 node116Labels := by rfl

def raw39875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39875Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39875step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw39875step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39875step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39875 raw39875Labels = mixedMoment B node17 node17Labels := by
  calc
    mixedMoment B raw39875 raw39875Labels = mixedMoment B raw39875step0 raw39875step0Labels := by
      have hz : ∀ j, raw39875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39875step0 = (fun i j => raw39875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39875step0 raw39875; decide +kernel
      have hl : raw39875step0Labels = raw39875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39875 raw39875Labels permutation434 hz
    mixedMoment B raw39875step0 raw39875step0Labels = mixedMoment B raw39875step1 raw39875step1Labels := by
      have hz : ∀ j, raw39875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39875step1 = (fun i j => raw39875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39875step1 raw39875step0; decide +kernel
      have hl : raw39875step1Labels = raw39875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39875step0 raw39875step0Labels permutation80 hz
    mixedMoment B raw39875step1 raw39875step1Labels = mixedMoment B raw39875step2 raw39875step2Labels := by
      have ha : raw39875step2 = (fun i j => raw39875step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39875step2 raw39875step1; decide +kernel
      have hl : raw39875step2Labels = raw39875step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39875step1 raw39875step1Labels permutation30 permutation6
    _ = mixedMoment B node17 node17Labels := by rfl

def raw39876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39876Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39876step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![2, -3, 1]]
def raw39876step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]
def raw39876step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw39876step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39876step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39876 raw39876Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39876 raw39876Labels = mixedMoment B raw39876step0 raw39876step0Labels := by
      have hz : ∀ j, raw39876 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39876step0 = (fun i j => raw39876 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39876step0 raw39876; decide +kernel
      have hl : raw39876step0Labels = raw39876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39876 raw39876Labels permutation520 hz
    mixedMoment B raw39876step0 raw39876step0Labels = mixedMoment B raw39876step1 raw39876step1Labels := by
      have hz : ∀ j, raw39876step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39876step1 = (fun i j => raw39876step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39876step1 raw39876step0; decide +kernel
      have hl : raw39876step1Labels = raw39876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39876step0 raw39876step0Labels permutation104 hz
    mixedMoment B raw39876step1 raw39876step1Labels = mixedMoment B raw39876step2 raw39876step2Labels := by
      have hz : ∀ j, raw39876step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39876step2 = (fun i j => raw39876step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39876step2 raw39876step1; decide +kernel
      have hl : raw39876step2Labels = raw39876step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39876step1 raw39876step1Labels permutation20 hz
    mixedMoment B raw39876step2 raw39876step2Labels = mixedMoment B raw39876step3 raw39876step3Labels := by
      have ha : raw39876step3 = (fun i j => raw39876step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39876step3 raw39876step2; decide +kernel
      have hl : raw39876step3Labels = raw39876step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39876step2 raw39876step2Labels permutation4 permutation4
    mixedMoment B raw39876step3 raw39876step3Labels = mixedMoment B raw39876step4 raw39876step4Labels := by
      have ha : raw39876step4 = -raw39876step3 := by apply Matrix.ext; change ∀ i j, raw39876step4 i j = -(raw39876step3 i j); unfold raw39876step4 raw39876step3; decide +kernel
      have hl : raw39876step4Labels = raw39876step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node270 node270Labels := by rfl

def raw39877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39877Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39877step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![2, -2, 0]]
def raw39877step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39877step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39877step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39877 raw39877Labels = mixedMoment B node269 node269Labels := by
  calc
    mixedMoment B raw39877 raw39877Labels = mixedMoment B raw39877step0 raw39877step0Labels := by
      have hz : ∀ j, raw39877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39877step0 = (fun i j => raw39877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39877step0 raw39877; decide +kernel
      have hl : raw39877step0Labels = raw39877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39877 raw39877Labels permutation434 hz
    mixedMoment B raw39877step0 raw39877step0Labels = mixedMoment B raw39877step1 raw39877step1Labels := by
      have hz : ∀ j, raw39877step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39877step1 = (fun i j => raw39877step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39877step1 raw39877step0; decide +kernel
      have hl : raw39877step1Labels = raw39877step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39877step0 raw39877step0Labels permutation80 hz
    mixedMoment B raw39877step1 raw39877step1Labels = mixedMoment B raw39877step2 raw39877step2Labels := by
      have ha : raw39877step2 = (fun i j => raw39877step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39877step2 raw39877step1; decide +kernel
      have hl : raw39877step2Labels = raw39877step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39877step1 raw39877step1Labels permutation14 permutation4
    mixedMoment B raw39877step2 raw39877step2Labels = mixedMoment B raw39877step3 raw39877step3Labels := by
      have ha : raw39877step3 = -raw39877step2 := by apply Matrix.ext; change ∀ i j, raw39877step3 i j = -(raw39877step2 i j); unfold raw39877step3 raw39877step2; decide +kernel
      have hl : raw39877step3Labels = raw39877step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node269 node269Labels := by rfl

def raw39878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39878Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39878step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![2, -1, -1]]
def raw39878step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39878step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39878 raw39878Labels = mixedMoment B node251 node251Labels := by
  calc
    mixedMoment B raw39878 raw39878Labels = mixedMoment B raw39878step0 raw39878step0Labels := by
      have hz : ∀ j, raw39878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39878step0 = (fun i j => raw39878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39878step0 raw39878; decide +kernel
      have hl : raw39878step0Labels = raw39878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39878 raw39878Labels permutation434 hz
    mixedMoment B raw39878step0 raw39878step0Labels = mixedMoment B raw39878step1 raw39878step1Labels := by
      have hz : ∀ j, raw39878step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39878step1 = (fun i j => raw39878step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39878step1 raw39878step0; decide +kernel
      have hl : raw39878step1Labels = raw39878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39878step0 raw39878step0Labels permutation80 hz
    mixedMoment B raw39878step1 raw39878step1Labels = mixedMoment B raw39878step2 raw39878step2Labels := by
      have ha : raw39878step2 = (fun i j => raw39878step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39878step2 raw39878step1; decide +kernel
      have hl : raw39878step2Labels = raw39878step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39878step1 raw39878step1Labels permutation18 permutation6
    _ = mixedMoment B node251 node251Labels := by rfl

def raw39879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39879Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39879step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -3, 3], ![2, 0, -2]]
def raw39879step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw39879step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39879 raw39879Labels = mixedMoment B node185 node185Labels := by
  calc
    mixedMoment B raw39879 raw39879Labels = mixedMoment B raw39879step0 raw39879step0Labels := by
      have hz : ∀ j, raw39879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39879step0 = (fun i j => raw39879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39879step0 raw39879; decide +kernel
      have hl : raw39879step0Labels = raw39879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39879 raw39879Labels permutation434 hz
    mixedMoment B raw39879step0 raw39879step0Labels = mixedMoment B raw39879step1 raw39879step1Labels := by
      have hz : ∀ j, raw39879step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39879step1 = (fun i j => raw39879step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39879step1 raw39879step0; decide +kernel
      have hl : raw39879step1Labels = raw39879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39879step0 raw39879step0Labels permutation80 hz
    mixedMoment B raw39879step1 raw39879step1Labels = mixedMoment B raw39879step2 raw39879step2Labels := by
      have ha : raw39879step2 = (fun i j => raw39879step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39879step2 raw39879step1; decide +kernel
      have hl : raw39879step2Labels = raw39879step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39879step1 raw39879step1Labels permutation18 permutation6
    _ = mixedMoment B node185 node185Labels := by rfl

def raw39880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39880Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39880step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39880step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39880step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39880 raw39880Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39880 raw39880Labels = mixedMoment B raw39880step0 raw39880step0Labels := by
      have hz : ∀ j, raw39880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39880step0 = (fun i j => raw39880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39880step0 raw39880; decide +kernel
      have hl : raw39880step0Labels = raw39880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39880 raw39880Labels permutation434 hz
    mixedMoment B raw39880step0 raw39880step0Labels = mixedMoment B raw39880step1 raw39880step1Labels := by
      have hz : ∀ j, raw39880step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39880step1 = (fun i j => raw39880step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39880step1 raw39880step0; decide +kernel
      have hl : raw39880step1Labels = raw39880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39880step0 raw39880step0Labels permutation80 hz
    mixedMoment B raw39880step1 raw39880step1Labels = mixedMoment B raw39880step2 raw39880step2Labels := by
      have ha : raw39880step2 = (fun i j => raw39880step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39880step2 raw39880step1; decide +kernel
      have hl : raw39880step2Labels = raw39880step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39880step1 raw39880step1Labels permutation17 permutation6
    _ = mixedMoment B node268 node268Labels := by rfl

def raw39881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw39881Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw39881step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39881step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39881 raw39881Labels = mixedMoment B node248 node248Labels := by
  calc
    mixedMoment B raw39881 raw39881Labels = mixedMoment B raw39881step0 raw39881step0Labels := by
      have hz : ∀ j, raw39881 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39881step0 = (fun i j => raw39881 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39881step0 raw39881; decide +kernel
      have hl : raw39881step0Labels = raw39881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39881 raw39881Labels permutation346 hz
    mixedMoment B raw39881step0 raw39881step0Labels = mixedMoment B raw39881step1 raw39881step1Labels := by
      have ha : raw39881step1 = (fun i j => raw39881step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39881step1 raw39881step0; decide +kernel
      have hl : raw39881step1Labels = raw39881step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39881step0 raw39881step0Labels permutation77 permutation6
    _ = mixedMoment B node248 node248Labels := by rfl

def raw39882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39882Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39882step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39882step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39882 raw39882Labels = mixedMoment B node182 node182Labels := by
  calc
    mixedMoment B raw39882 raw39882Labels = mixedMoment B raw39882step0 raw39882step0Labels := by
      have hz : ∀ j, raw39882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39882step0 = (fun i j => raw39882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39882step0 raw39882; decide +kernel
      have hl : raw39882step0Labels = raw39882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39882 raw39882Labels permutation346 hz
    mixedMoment B raw39882step0 raw39882step0Labels = mixedMoment B raw39882step1 raw39882step1Labels := by
      have ha : raw39882step1 = (fun i j => raw39882step0 (permutation76 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39882step1 raw39882step0; decide +kernel
      have hl : raw39882step1Labels = raw39882step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39882step0 raw39882step0Labels permutation76 permutation6
    _ = mixedMoment B node182 node182Labels := by rfl

def raw39883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39883Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39883step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39883step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39883 raw39883Labels = mixedMoment B node235 node235Labels := by
  calc
    mixedMoment B raw39883 raw39883Labels = mixedMoment B raw39883step0 raw39883step0Labels := by
      have hz : ∀ j, raw39883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39883step0 = (fun i j => raw39883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39883step0 raw39883; decide +kernel
      have hl : raw39883step0Labels = raw39883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39883 raw39883Labels permutation346 hz
    mixedMoment B raw39883step0 raw39883step0Labels = mixedMoment B raw39883step1 raw39883step1Labels := by
      have ha : raw39883step1 = (fun i j => raw39883step0 (permutation71 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39883step1 raw39883step0; decide +kernel
      have hl : raw39883step1Labels = raw39883step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39883step0 raw39883step0Labels permutation71 permutation6
    _ = mixedMoment B node235 node235Labels := by rfl

def raw39884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39884Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39884step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39884step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39884 raw39884Labels = mixedMoment B node261 node261Labels := by
  calc
    mixedMoment B raw39884 raw39884Labels = mixedMoment B raw39884step0 raw39884step0Labels := by
      have hz : ∀ j, raw39884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39884step0 = (fun i j => raw39884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39884step0 raw39884; decide +kernel
      have hl : raw39884step0Labels = raw39884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39884 raw39884Labels permutation346 hz
    mixedMoment B raw39884step0 raw39884step0Labels = mixedMoment B raw39884step1 raw39884step1Labels := by
      have ha : raw39884step1 = (fun i j => raw39884step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39884step1 raw39884step0; decide +kernel
      have hl : raw39884step1Labels = raw39884step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39884step0 raw39884step0Labels permutation73 permutation6
    _ = mixedMoment B node261 node261Labels := by rfl

def raw39885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39885Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39885step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw39885step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw39885step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39885 raw39885Labels = mixedMoment B node173 node173Labels := by
  calc
    mixedMoment B raw39885 raw39885Labels = mixedMoment B raw39885step0 raw39885step0Labels := by
      have hz : ∀ j, raw39885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39885step0 = (fun i j => raw39885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39885step0 raw39885; decide +kernel
      have hl : raw39885step0Labels = raw39885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39885 raw39885Labels permutation346 hz
    mixedMoment B raw39885step0 raw39885step0Labels = mixedMoment B raw39885step1 raw39885step1Labels := by
      have ha : raw39885step1 = (fun i j => raw39885step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39885step1 raw39885step0; decide +kernel
      have hl : raw39885step1Labels = raw39885step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39885step0 raw39885step0Labels permutation83 permutation6
    mixedMoment B raw39885step1 raw39885step1Labels = mixedMoment B raw39885step2 raw39885step2Labels := by
      have ha : raw39885step2 = -raw39885step1 := by apply Matrix.ext; change ∀ i j, raw39885step2 i j = -(raw39885step1 i j); unfold raw39885step2 raw39885step1; decide +kernel
      have hl : raw39885step2Labels = raw39885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node173 node173Labels := by rfl

def raw39886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39886Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39886step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39886 raw39886Labels = mixedMoment B node179 node179Labels := by
  calc
    mixedMoment B raw39886 raw39886Labels = mixedMoment B raw39886step0 raw39886step0Labels := by
      have ha : raw39886step0 = (fun i j => raw39886 (permutation340 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39886step0 raw39886; decide +kernel
      have hl : raw39886step0Labels = raw39886Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39886 raw39886Labels permutation340 permutation6
    _ = mixedMoment B node179 node179Labels := by rfl

def raw39887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39887Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39887step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39887 raw39887Labels = mixedMoment B node223 node223Labels := by
  calc
    mixedMoment B raw39887 raw39887Labels = mixedMoment B raw39887step0 raw39887step0Labels := by
      have ha : raw39887step0 = (fun i j => raw39887 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39887step0 raw39887; decide +kernel
      have hl : raw39887step0Labels = raw39887Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39887 raw39887Labels permutation332 permutation6
    _ = mixedMoment B node223 node223Labels := by rfl

def raw39888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39888Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39888step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39888 raw39888Labels = mixedMoment B node209 node209Labels := by
  calc
    mixedMoment B raw39888 raw39888Labels = mixedMoment B raw39888step0 raw39888step0Labels := by
      have ha : raw39888step0 = (fun i j => raw39888 (permutation331 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39888step0 raw39888; decide +kernel
      have hl : raw39888step0Labels = raw39888Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39888 raw39888Labels permutation331 permutation6
    _ = mixedMoment B node209 node209Labels := by rfl

def raw39889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39889Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw39889step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![2, -3, 1]]
def raw39889step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39889step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39889 raw39889Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39889 raw39889Labels = mixedMoment B raw39889step0 raw39889step0Labels := by
      have hz : ∀ j, raw39889 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39889step0 = (fun i j => raw39889 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39889step0 raw39889; decide +kernel
      have hl : raw39889step0Labels = raw39889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39889 raw39889Labels permutation520 hz
    mixedMoment B raw39889step0 raw39889step0Labels = mixedMoment B raw39889step1 raw39889step1Labels := by
      have hz : ∀ j, raw39889step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39889step1 = (fun i j => raw39889step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39889step1 raw39889step0; decide +kernel
      have hl : raw39889step1Labels = raw39889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39889step0 raw39889step0Labels permutation104 hz
    mixedMoment B raw39889step1 raw39889step1Labels = mixedMoment B raw39889step2 raw39889step2Labels := by
      have ha : raw39889step2 = (fun i j => raw39889step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39889step2 raw39889step1; decide +kernel
      have hl : raw39889step2Labels = raw39889step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39889step1 raw39889step1Labels permutation27 permutation5
    _ = mixedMoment B node412 node412Labels := by rfl

def raw39890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39890Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39890step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39890step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39890step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39890 raw39890Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw39890 raw39890Labels = mixedMoment B raw39890step0 raw39890step0Labels := by
      have hz : ∀ j, raw39890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39890step0 = (fun i j => raw39890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39890step0 raw39890; decide +kernel
      have hl : raw39890step0Labels = raw39890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39890 raw39890Labels permutation434 hz
    mixedMoment B raw39890step0 raw39890step0Labels = mixedMoment B raw39890step1 raw39890step1Labels := by
      have ha : raw39890step1 = (fun i j => raw39890step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39890step1 raw39890step0; decide +kernel
      have hl : raw39890step1Labels = raw39890step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39890step0 raw39890step0Labels permutation62 permutation4
    mixedMoment B raw39890step1 raw39890step1Labels = mixedMoment B raw39890step2 raw39890step2Labels := by
      have ha : raw39890step2 = -raw39890step1 := by apply Matrix.ext; change ∀ i j, raw39890step2 i j = -(raw39890step1 i j); unfold raw39890step2 raw39890step1; decide +kernel
      have hl : raw39890step2Labels = raw39890step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node468 node468Labels := by rfl

def raw39891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39891Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39891step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39891step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39891 raw39891Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39891 raw39891Labels = mixedMoment B raw39891step0 raw39891step0Labels := by
      have hz : ∀ j, raw39891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39891step0 = (fun i j => raw39891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39891step0 raw39891; decide +kernel
      have hl : raw39891step0Labels = raw39891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39891 raw39891Labels permutation434 hz
    mixedMoment B raw39891step0 raw39891step0Labels = mixedMoment B raw39891step1 raw39891step1Labels := by
      have ha : raw39891step1 = (fun i j => raw39891step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39891step1 raw39891step0; decide +kernel
      have hl : raw39891step1Labels = raw39891step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39891step0 raw39891step0Labels permutation65 permutation6
    _ = mixedMoment B node467 node467Labels := by rfl

def raw39892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39892Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39892step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39892 raw39892Labels = mixedMoment B node439 node439Labels := by
  calc
    mixedMoment B raw39892 raw39892Labels = mixedMoment B raw39892step0 raw39892step0Labels := by
      have ha : raw39892step0 = (fun i j => raw39892 (permutation339 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39892step0 raw39892; decide +kernel
      have hl : raw39892step0Labels = raw39892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39892 raw39892Labels permutation339 permutation6
    _ = mixedMoment B node439 node439Labels := by rfl

def raw39893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39893Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39893step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39893 raw39893Labels = mixedMoment B node455 node455Labels := by
  calc
    mixedMoment B raw39893 raw39893Labels = mixedMoment B raw39893step0 raw39893step0Labels := by
      have ha : raw39893step0 = (fun i j => raw39893 (permutation301 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39893step0 raw39893; decide +kernel
      have hl : raw39893step0Labels = raw39893Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39893 raw39893Labels permutation301 permutation6
    _ = mixedMoment B node455 node455Labels := by rfl

def raw39894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39894Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw39894step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39894step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39894 raw39894Labels = mixedMoment B node171 node171Labels := by
  calc
    mixedMoment B raw39894 raw39894Labels = mixedMoment B raw39894step0 raw39894step0Labels := by
      have ha : raw39894step0 = (fun i j => raw39894 (permutation447 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39894step0 raw39894; decide +kernel
      have hl : raw39894step0Labels = raw39894Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39894 raw39894Labels permutation447 permutation6
    mixedMoment B raw39894step0 raw39894step0Labels = mixedMoment B raw39894step1 raw39894step1Labels := by
      have ha : raw39894step1 = -raw39894step0 := by apply Matrix.ext; change ∀ i j, raw39894step1 i j = -(raw39894step0 i j); unfold raw39894step1 raw39894step0; decide +kernel
      have hl : raw39894step1Labels = raw39894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node171 node171Labels := by rfl

def raw39895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39895Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39895step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw39895step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw39895step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39895 raw39895Labels = mixedMoment B node507 node507Labels := by
  calc
    mixedMoment B raw39895 raw39895Labels = mixedMoment B raw39895step0 raw39895step0Labels := by
      have hz : ∀ j, raw39895 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39895step0 = (fun i j => raw39895 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39895step0 raw39895; decide +kernel
      have hl : raw39895step0Labels = raw39895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39895 raw39895Labels permutation520 hz
    mixedMoment B raw39895step0 raw39895step0Labels = mixedMoment B raw39895step1 raw39895step1Labels := by
      have hz : ∀ j, raw39895step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39895step1 = (fun i j => raw39895step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39895step1 raw39895step0; decide +kernel
      have hl : raw39895step1Labels = raw39895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39895step0 raw39895step0Labels permutation104 hz
    mixedMoment B raw39895step1 raw39895step1Labels = mixedMoment B raw39895step2 raw39895step2Labels := by
      have hz : ∀ j, raw39895step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39895step2 = (fun i j => raw39895step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39895step2 raw39895step1; decide +kernel
      have hl : raw39895step2Labels = raw39895step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39895step1 raw39895step1Labels permutation20 hz
    _ = mixedMoment B node507 node507Labels := by rfl

def raw39896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39896Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39896step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw39896step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw39896step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39896step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39896 raw39896Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39896 raw39896Labels = mixedMoment B raw39896step0 raw39896step0Labels := by
      have hz : ∀ j, raw39896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39896step0 = (fun i j => raw39896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39896step0 raw39896; decide +kernel
      have hl : raw39896step0Labels = raw39896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39896 raw39896Labels permutation434 hz
    mixedMoment B raw39896step0 raw39896step0Labels = mixedMoment B raw39896step1 raw39896step1Labels := by
      have hz : ∀ j, raw39896step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39896step1 = (fun i j => raw39896step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39896step1 raw39896step0; decide +kernel
      have hl : raw39896step1Labels = raw39896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39896step0 raw39896step0Labels permutation80 hz
    mixedMoment B raw39896step1 raw39896step1Labels = mixedMoment B raw39896step2 raw39896step2Labels := by
      have ha : raw39896step2 = (fun i j => raw39896step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39896step2 raw39896step1; decide +kernel
      have hl : raw39896step2Labels = raw39896step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39896step1 raw39896step1Labels permutation11 permutation7
    mixedMoment B raw39896step2 raw39896step2Labels = mixedMoment B raw39896step3 raw39896step3Labels := by
      have ha : raw39896step3 = -raw39896step2 := by apply Matrix.ext; change ∀ i j, raw39896step3 i j = -(raw39896step2 i j); unfold raw39896step3 raw39896step2; decide +kernel
      have hl : raw39896step3Labels = raw39896step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

def raw39897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39897Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39897step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]
def raw39897step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39897step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39897 raw39897Labels = mixedMoment B node451 node451Labels := by
  calc
    mixedMoment B raw39897 raw39897Labels = mixedMoment B raw39897step0 raw39897step0Labels := by
      have hz : ∀ j, raw39897 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39897step0 = (fun i j => raw39897 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39897step0 raw39897; decide +kernel
      have hl : raw39897step0Labels = raw39897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39897 raw39897Labels permutation434 hz
    mixedMoment B raw39897step0 raw39897step0Labels = mixedMoment B raw39897step1 raw39897step1Labels := by
      have hz : ∀ j, raw39897step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39897step1 = (fun i j => raw39897step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39897step1 raw39897step0; decide +kernel
      have hl : raw39897step1Labels = raw39897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39897step0 raw39897step0Labels permutation80 hz
    mixedMoment B raw39897step1 raw39897step1Labels = mixedMoment B raw39897step2 raw39897step2Labels := by
      have ha : raw39897step2 = (fun i j => raw39897step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39897step2 raw39897step1; decide +kernel
      have hl : raw39897step2Labels = raw39897step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39897step1 raw39897step1Labels permutation18 permutation6
    _ = mixedMoment B node451 node451Labels := by rfl

def raw39898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39898Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39898step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 1, -2], ![1, -3, 2]]
def raw39898step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw39898step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39898 raw39898Labels = mixedMoment B node369 node369Labels := by
  calc
    mixedMoment B raw39898 raw39898Labels = mixedMoment B raw39898step0 raw39898step0Labels := by
      have hz : ∀ j, raw39898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39898step0 = (fun i j => raw39898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39898step0 raw39898; decide +kernel
      have hl : raw39898step0Labels = raw39898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39898 raw39898Labels permutation434 hz
    mixedMoment B raw39898step0 raw39898step0Labels = mixedMoment B raw39898step1 raw39898step1Labels := by
      have hz : ∀ j, raw39898step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39898step1 = (fun i j => raw39898step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39898step1 raw39898step0; decide +kernel
      have hl : raw39898step1Labels = raw39898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39898step0 raw39898step0Labels permutation80 hz
    mixedMoment B raw39898step1 raw39898step1Labels = mixedMoment B raw39898step2 raw39898step2Labels := by
      have ha : raw39898step2 = (fun i j => raw39898step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39898step2 raw39898step1; decide +kernel
      have hl : raw39898step2Labels = raw39898step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39898step1 raw39898step1Labels permutation27 permutation4
    _ = mixedMoment B node369 node369Labels := by rfl

def raw39899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39899Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39899step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39899step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39899step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39899 raw39899Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39899 raw39899Labels = mixedMoment B raw39899step0 raw39899step0Labels := by
      have hz : ∀ j, raw39899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39899step0 = (fun i j => raw39899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39899step0 raw39899; decide +kernel
      have hl : raw39899step0Labels = raw39899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39899 raw39899Labels permutation434 hz
    mixedMoment B raw39899step0 raw39899step0Labels = mixedMoment B raw39899step1 raw39899step1Labels := by
      have hz : ∀ j, raw39899step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39899step1 = (fun i j => raw39899step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39899step1 raw39899step0; decide +kernel
      have hl : raw39899step1Labels = raw39899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39899step0 raw39899step0Labels permutation80 hz
    mixedMoment B raw39899step1 raw39899step1Labels = mixedMoment B raw39899step2 raw39899step2Labels := by
      have ha : raw39899step2 = (fun i j => raw39899step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39899step2 raw39899step1; decide +kernel
      have hl : raw39899step2Labels = raw39899step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39899step1 raw39899step1Labels permutation17 permutation6
    _ = mixedMoment B node496 node496Labels := by rfl

def raw39900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39900Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39900step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39900step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39900step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39900 raw39900Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw39900 raw39900Labels = mixedMoment B raw39900step0 raw39900step0Labels := by
      have hz : ∀ j, raw39900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39900step0 = (fun i j => raw39900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39900step0 raw39900; decide +kernel
      have hl : raw39900step0Labels = raw39900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39900 raw39900Labels permutation434 hz
    mixedMoment B raw39900step0 raw39900step0Labels = mixedMoment B raw39900step1 raw39900step1Labels := by
      have hz : ∀ j, raw39900step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39900step1 = (fun i j => raw39900step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39900step1 raw39900step0; decide +kernel
      have hl : raw39900step1Labels = raw39900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39900step0 raw39900step0Labels permutation80 hz
    mixedMoment B raw39900step1 raw39900step1Labels = mixedMoment B raw39900step2 raw39900step2Labels := by
      have ha : raw39900step2 = (fun i j => raw39900step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39900step2 raw39900step1; decide +kernel
      have hl : raw39900step2Labels = raw39900step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39900step1 raw39900step1Labels permutation17 permutation6
    _ = mixedMoment B node505 node505Labels := by rfl

def raw39901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39901Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39901step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39901step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39901 raw39901Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw39901 raw39901Labels = mixedMoment B raw39901step0 raw39901step0Labels := by
      have hz : ∀ j, raw39901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39901step0 = (fun i j => raw39901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39901step0 raw39901; decide +kernel
      have hl : raw39901step0Labels = raw39901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39901 raw39901Labels permutation346 hz
    mixedMoment B raw39901step0 raw39901step0Labels = mixedMoment B raw39901step1 raw39901step1Labels := by
      have ha : raw39901step1 = (fun i j => raw39901step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39901step1 raw39901step0; decide +kernel
      have hl : raw39901step1Labels = raw39901step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39901step0 raw39901step0Labels permutation137 permutation7
    _ = mixedMoment B node449 node449Labels := by rfl

def raw39902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39902Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39902step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39902step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39902 raw39902Labels = mixedMoment B node286 node286Labels := by
  calc
    mixedMoment B raw39902 raw39902Labels = mixedMoment B raw39902step0 raw39902step0Labels := by
      have hz : ∀ j, raw39902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39902step0 = (fun i j => raw39902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39902step0 raw39902; decide +kernel
      have hl : raw39902step0Labels = raw39902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39902 raw39902Labels permutation346 hz
    mixedMoment B raw39902step0 raw39902step0Labels = mixedMoment B raw39902step1 raw39902step1Labels := by
      have ha : raw39902step1 = (fun i j => raw39902step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39902step1 raw39902step0; decide +kernel
      have hl : raw39902step1Labels = raw39902step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39902step0 raw39902step0Labels permutation137 permutation7
    _ = mixedMoment B node286 node286Labels := by rfl

def raw39903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39903Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39903step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39903step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39903 raw39903Labels = mixedMoment B node438 node438Labels := by
  calc
    mixedMoment B raw39903 raw39903Labels = mixedMoment B raw39903step0 raw39903step0Labels := by
      have hz : ∀ j, raw39903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39903step0 = (fun i j => raw39903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39903step0 raw39903; decide +kernel
      have hl : raw39903step0Labels = raw39903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39903 raw39903Labels permutation346 hz
    mixedMoment B raw39903step0 raw39903step0Labels = mixedMoment B raw39903step1 raw39903step1Labels := by
      have ha : raw39903step1 = (fun i j => raw39903step0 (permutation71 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39903step1 raw39903step0; decide +kernel
      have hl : raw39903step1Labels = raw39903step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39903step0 raw39903step0Labels permutation71 permutation6
    _ = mixedMoment B node438 node438Labels := by rfl

def raw39904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39904Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39904step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39904step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39904 raw39904Labels = mixedMoment B node490 node490Labels := by
  calc
    mixedMoment B raw39904 raw39904Labels = mixedMoment B raw39904step0 raw39904step0Labels := by
      have hz : ∀ j, raw39904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39904step0 = (fun i j => raw39904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39904step0 raw39904; decide +kernel
      have hl : raw39904step0Labels = raw39904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39904 raw39904Labels permutation346 hz
    mixedMoment B raw39904step0 raw39904step0Labels = mixedMoment B raw39904step1 raw39904step1Labels := by
      have ha : raw39904step1 = (fun i j => raw39904step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39904step1 raw39904step0; decide +kernel
      have hl : raw39904step1Labels = raw39904step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39904step0 raw39904step0Labels permutation73 permutation6
    _ = mixedMoment B node490 node490Labels := by rfl

def raw39905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39905Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39905step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39905step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39905 raw39905Labels = mixedMoment B node432 node432Labels := by
  calc
    mixedMoment B raw39905 raw39905Labels = mixedMoment B raw39905step0 raw39905step0Labels := by
      have hz : ∀ j, raw39905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39905step0 = (fun i j => raw39905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39905step0 raw39905; decide +kernel
      have hl : raw39905step0Labels = raw39905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39905 raw39905Labels permutation346 hz
    mixedMoment B raw39905step0 raw39905step0Labels = mixedMoment B raw39905step1 raw39905step1Labels := by
      have ha : raw39905step1 = (fun i j => raw39905step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39905step1 raw39905step0; decide +kernel
      have hl : raw39905step1Labels = raw39905step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39905step0 raw39905step0Labels permutation72 permutation6
    _ = mixedMoment B node432 node432Labels := by rfl

def raw39906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39906Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39906step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39906step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39906step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39906 raw39906Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw39906 raw39906Labels = mixedMoment B raw39906step0 raw39906step0Labels := by
      have hz : ∀ j, raw39906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39906step0 = (fun i j => raw39906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39906step0 raw39906; decide +kernel
      have hl : raw39906step0Labels = raw39906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39906 raw39906Labels permutation346 hz
    mixedMoment B raw39906step0 raw39906step0Labels = mixedMoment B raw39906step1 raw39906step1Labels := by
      have ha : raw39906step1 = (fun i j => raw39906step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39906step1 raw39906step0; decide +kernel
      have hl : raw39906step1Labels = raw39906step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39906step0 raw39906step0Labels permutation83 permutation6
    mixedMoment B raw39906step1 raw39906step1Labels = mixedMoment B raw39906step2 raw39906step2Labels := by
      have ha : raw39906step2 = -raw39906step1 := by apply Matrix.ext; change ∀ i j, raw39906step2 i j = -(raw39906step1 i j); unfold raw39906step2 raw39906step1; decide +kernel
      have hl : raw39906step2Labels = raw39906step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node449 node449Labels := by rfl

def raw39907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39907Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39907step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw39907step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39907step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39907 raw39907Labels = mixedMoment B node178 node178Labels := by
  calc
    mixedMoment B raw39907 raw39907Labels = mixedMoment B raw39907step0 raw39907step0Labels := by
      have hz : ∀ j, raw39907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39907step0 = (fun i j => raw39907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39907step0 raw39907; decide +kernel
      have hl : raw39907step0Labels = raw39907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39907 raw39907Labels permutation346 hz
    mixedMoment B raw39907step0 raw39907step0Labels = mixedMoment B raw39907step1 raw39907step1Labels := by
      have ha : raw39907step1 = (fun i j => raw39907step0 (permutation85 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39907step1 raw39907step0; decide +kernel
      have hl : raw39907step1Labels = raw39907step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39907step0 raw39907step0Labels permutation85 permutation6
    mixedMoment B raw39907step1 raw39907step1Labels = mixedMoment B raw39907step2 raw39907step2Labels := by
      have ha : raw39907step2 = -raw39907step1 := by apply Matrix.ext; change ∀ i j, raw39907step2 i j = -(raw39907step1 i j); unfold raw39907step2 raw39907step1; decide +kernel
      have hl : raw39907step2Labels = raw39907step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node178 node178Labels := by rfl

def raw39908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39908Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39908step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39908 raw39908Labels = mixedMoment B node424 node424Labels := by
  calc
    mixedMoment B raw39908 raw39908Labels = mixedMoment B raw39908step0 raw39908step0Labels := by
      have ha : raw39908step0 = (fun i j => raw39908 (permutation331 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39908step0 raw39908; decide +kernel
      have hl : raw39908step0Labels = raw39908Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39908 raw39908Labels permutation331 permutation6
    _ = mixedMoment B node424 node424Labels := by rfl

def raw39909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39909Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39909step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39909 raw39909Labels = mixedMoment B node492 node492Labels := by
  calc
    mixedMoment B raw39909 raw39909Labels = mixedMoment B raw39909step0 raw39909step0Labels := by
      have ha : raw39909step0 = (fun i j => raw39909 (permutation665 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39909step0 raw39909; decide +kernel
      have hl : raw39909step0Labels = raw39909Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39909 raw39909Labels permutation665 permutation5
    _ = mixedMoment B node492 node492Labels := by rfl

def raw39910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw39910Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39910step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39910step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39910step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39910 raw39910Labels = mixedMoment B node179 node179Labels := by
  calc
    mixedMoment B raw39910 raw39910Labels = mixedMoment B raw39910step0 raw39910step0Labels := by
      have ha : raw39910step0 = (fun i j => raw39910 (permutation520 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39910step0 raw39910; decide +kernel
      have hl : raw39910step0Labels = raw39910Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39910 raw39910Labels permutation520 permutation6
    mixedMoment B raw39910step0 raw39910step0Labels = mixedMoment B raw39910step1 raw39910step1Labels := by
      have ha : raw39910step1 = -raw39910step0 := by apply Matrix.ext; change ∀ i j, raw39910step1 i j = -(raw39910step0 i j); unfold raw39910step1 raw39910step0; decide +kernel
      have hl : raw39910step1Labels = raw39910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node179 node179Labels := by rfl

def raw39911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39911Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw39911step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39911step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39911 raw39911Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw39911 raw39911Labels = mixedMoment B raw39911step0 raw39911step0Labels := by
      have hz : ∀ j, raw39911 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39911step0 = (fun i j => raw39911 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39911step0 raw39911; decide +kernel
      have hl : raw39911step0Labels = raw39911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39911 raw39911Labels permutation520 hz
    mixedMoment B raw39911step0 raw39911step0Labels = mixedMoment B raw39911step1 raw39911step1Labels := by
      have hz : ∀ j, raw39911step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39911step1 = (fun i j => raw39911step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39911step1 raw39911step0; decide +kernel
      have hl : raw39911step1Labels = raw39911step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39911step0 raw39911step0Labels permutation104 hz
    _ = mixedMoment B node505 node505Labels := by rfl

def raw39912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39912Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw39912step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39912step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39912step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39912 raw39912Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw39912 raw39912Labels = mixedMoment B raw39912step0 raw39912step0Labels := by
      have hz : ∀ j, raw39912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39912step0 = (fun i j => raw39912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39912step0 raw39912; decide +kernel
      have hl : raw39912step0Labels = raw39912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39912 raw39912Labels permutation434 hz
    mixedMoment B raw39912step0 raw39912step0Labels = mixedMoment B raw39912step1 raw39912step1Labels := by
      have ha : raw39912step1 = (fun i j => raw39912step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39912step1 raw39912step0; decide +kernel
      have hl : raw39912step1Labels = raw39912step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39912step0 raw39912step0Labels permutation44 permutation7
    mixedMoment B raw39912step1 raw39912step1Labels = mixedMoment B raw39912step2 raw39912step2Labels := by
      have ha : raw39912step2 = -raw39912step1 := by apply Matrix.ext; change ∀ i j, raw39912step2 i j = -(raw39912step1 i j); unfold raw39912step2 raw39912step1; decide +kernel
      have hl : raw39912step2Labels = raw39912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node449 node449Labels := by rfl

def raw39913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw39913Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw39913step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw39913step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39913step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39913 raw39913Labels = mixedMoment B node180 node180Labels := by
  calc
    mixedMoment B raw39913 raw39913Labels = mixedMoment B raw39913step0 raw39913step0Labels := by
      have hz : ∀ j, raw39913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39913step0 = (fun i j => raw39913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39913step0 raw39913; decide +kernel
      have hl : raw39913step0Labels = raw39913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39913 raw39913Labels permutation434 hz
    mixedMoment B raw39913step0 raw39913step0Labels = mixedMoment B raw39913step1 raw39913step1Labels := by
      have ha : raw39913step1 = (fun i j => raw39913step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39913step1 raw39913step0; decide +kernel
      have hl : raw39913step1Labels = raw39913step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39913step0 raw39913step0Labels permutation104 permutation6
    mixedMoment B raw39913step1 raw39913step1Labels = mixedMoment B raw39913step2 raw39913step2Labels := by
      have ha : raw39913step2 = -raw39913step1 := by apply Matrix.ext; change ∀ i j, raw39913step2 i j = -(raw39913step1 i j); unfold raw39913step2 raw39913step1; decide +kernel
      have hl : raw39913step2Labels = raw39913step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node180 node180Labels := by rfl

def raw39914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39914Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39914step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39914 raw39914Labels = mixedMoment B node471 node471Labels := by
  calc
    mixedMoment B raw39914 raw39914Labels = mixedMoment B raw39914step0 raw39914step0Labels := by
      have ha : raw39914step0 = (fun i j => raw39914 (permutation609 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39914step0 raw39914; decide +kernel
      have hl : raw39914step0Labels = raw39914Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39914 raw39914Labels permutation609 permutation7
    _ = mixedMoment B node471 node471Labels := by rfl

def raw39915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39915Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39915step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39915 raw39915Labels = mixedMoment B node317 node317Labels := by
  calc
    mixedMoment B raw39915 raw39915Labels = mixedMoment B raw39915step0 raw39915step0Labels := by
      have ha : raw39915step0 = (fun i j => raw39915 (permutation609 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39915step0 raw39915; decide +kernel
      have hl : raw39915step0Labels = raw39915Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39915 raw39915Labels permutation609 permutation7
    _ = mixedMoment B node317 node317Labels := by rfl

def raw39916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39916Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39916step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39916step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39916 raw39916Labels = mixedMoment B node448 node448Labels := by
  calc
    mixedMoment B raw39916 raw39916Labels = mixedMoment B raw39916step0 raw39916step0Labels := by
      have ha : raw39916step0 = (fun i j => raw39916 (permutation446 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39916step0 raw39916; decide +kernel
      have hl : raw39916step0Labels = raw39916Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39916 raw39916Labels permutation446 permutation6
    mixedMoment B raw39916step0 raw39916step0Labels = mixedMoment B raw39916step1 raw39916step1Labels := by
      have ha : raw39916step1 = -raw39916step0 := by apply Matrix.ext; change ∀ i j, raw39916step1 i j = -(raw39916step0 i j); unfold raw39916step1 raw39916step0; decide +kernel
      have hl : raw39916step1Labels = raw39916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node448 node448Labels := by rfl

def raw39917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39917Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39917step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw39917step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39917step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39917 raw39917Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw39917 raw39917Labels = mixedMoment B raw39917step0 raw39917step0Labels := by
      have hz : ∀ j, raw39917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39917step0 = (fun i j => raw39917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39917step0 raw39917; decide +kernel
      have hl : raw39917step0Labels = raw39917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39917 raw39917Labels permutation434 hz
    mixedMoment B raw39917step0 raw39917step0Labels = mixedMoment B raw39917step1 raw39917step1Labels := by
      have hz : ∀ j, raw39917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39917step1 = (fun i j => raw39917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39917step1 raw39917step0; decide +kernel
      have hl : raw39917step1Labels = raw39917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39917step0 raw39917step0Labels permutation80 hz
    mixedMoment B raw39917step1 raw39917step1Labels = mixedMoment B raw39917step2 raw39917step2Labels := by
      have ha : raw39917step2 = (fun i j => raw39917step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39917step2 raw39917step1; decide +kernel
      have hl : raw39917step2Labels = raw39917step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39917step1 raw39917step1Labels permutation29 permutation7
    _ = mixedMoment B node343 node343Labels := by rfl

def raw39918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39918Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39918step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 2, -3], ![1, -3, 2]]
def raw39918step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39918step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39918 raw39918Labels = mixedMoment B node316 node316Labels := by
  calc
    mixedMoment B raw39918 raw39918Labels = mixedMoment B raw39918step0 raw39918step0Labels := by
      have hz : ∀ j, raw39918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39918step0 = (fun i j => raw39918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39918step0 raw39918; decide +kernel
      have hl : raw39918step0Labels = raw39918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39918 raw39918Labels permutation434 hz
    mixedMoment B raw39918step0 raw39918step0Labels = mixedMoment B raw39918step1 raw39918step1Labels := by
      have hz : ∀ j, raw39918step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39918step1 = (fun i j => raw39918step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39918step1 raw39918step0; decide +kernel
      have hl : raw39918step1Labels = raw39918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39918step0 raw39918step0Labels permutation80 hz
    mixedMoment B raw39918step1 raw39918step1Labels = mixedMoment B raw39918step2 raw39918step2Labels := by
      have ha : raw39918step2 = (fun i j => raw39918step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39918step2 raw39918step1; decide +kernel
      have hl : raw39918step2Labels = raw39918step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39918step1 raw39918step1Labels permutation22 permutation6
    _ = mixedMoment B node316 node316Labels := by rfl

def raw39919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39919Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39919step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39919step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39919 raw39919Labels = mixedMoment B node335 node335Labels := by
  calc
    mixedMoment B raw39919 raw39919Labels = mixedMoment B raw39919step0 raw39919step0Labels := by
      have hz : ∀ j, raw39919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39919step0 = (fun i j => raw39919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39919step0 raw39919; decide +kernel
      have hl : raw39919step0Labels = raw39919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39919 raw39919Labels permutation346 hz
    mixedMoment B raw39919step0 raw39919step0Labels = mixedMoment B raw39919step1 raw39919step1Labels := by
      have ha : raw39919step1 = (fun i j => raw39919step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39919step1 raw39919step0; decide +kernel
      have hl : raw39919step1Labels = raw39919step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39919step0 raw39919step0Labels permutation137 permutation7
    _ = mixedMoment B node335 node335Labels := by rfl

def raw39920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39920Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39920step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39920step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39920 raw39920Labels = mixedMoment B node127 node127Labels := by
  calc
    mixedMoment B raw39920 raw39920Labels = mixedMoment B raw39920step0 raw39920step0Labels := by
      have hz : ∀ j, raw39920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39920step0 = (fun i j => raw39920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39920step0 raw39920; decide +kernel
      have hl : raw39920step0Labels = raw39920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39920 raw39920Labels permutation346 hz
    mixedMoment B raw39920step0 raw39920step0Labels = mixedMoment B raw39920step1 raw39920step1Labels := by
      have ha : raw39920step1 = (fun i j => raw39920step0 (permutation136 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39920step1 raw39920step0; decide +kernel
      have hl : raw39920step1Labels = raw39920step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39920step0 raw39920step0Labels permutation136 permutation6
    _ = mixedMoment B node127 node127Labels := by rfl

def raw39921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39921Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39921step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39921step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39921 raw39921Labels = mixedMoment B node314 node314Labels := by
  calc
    mixedMoment B raw39921 raw39921Labels = mixedMoment B raw39921step0 raw39921step0Labels := by
      have hz : ∀ j, raw39921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39921step0 = (fun i j => raw39921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39921step0 raw39921; decide +kernel
      have hl : raw39921step0Labels = raw39921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39921 raw39921Labels permutation346 hz
    mixedMoment B raw39921step0 raw39921step0Labels = mixedMoment B raw39921step1 raw39921step1Labels := by
      have ha : raw39921step1 = (fun i j => raw39921step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39921step1 raw39921step0; decide +kernel
      have hl : raw39921step1Labels = raw39921step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39921step0 raw39921step0Labels permutation113 permutation6
    _ = mixedMoment B node314 node314Labels := by rfl

def raw39922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39922Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39922step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39922step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39922 raw39922Labels = mixedMoment B node306 node306Labels := by
  calc
    mixedMoment B raw39922 raw39922Labels = mixedMoment B raw39922step0 raw39922step0Labels := by
      have hz : ∀ j, raw39922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39922step0 = (fun i j => raw39922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39922step0 raw39922; decide +kernel
      have hl : raw39922step0Labels = raw39922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39922 raw39922Labels permutation346 hz
    mixedMoment B raw39922step0 raw39922step0Labels = mixedMoment B raw39922step1 raw39922step1Labels := by
      have ha : raw39922step1 = (fun i j => raw39922step0 (permutation114 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39922step1 raw39922step0; decide +kernel
      have hl : raw39922step1Labels = raw39922step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39922step0 raw39922step0Labels permutation114 permutation6
    _ = mixedMoment B node306 node306Labels := by rfl

def raw39923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39923Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39923step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw39923step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39923step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39923 raw39923Labels = mixedMoment B node450 node450Labels := by
  calc
    mixedMoment B raw39923 raw39923Labels = mixedMoment B raw39923step0 raw39923step0Labels := by
      have hz : ∀ j, raw39923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39923step0 = (fun i j => raw39923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39923step0 raw39923; decide +kernel
      have hl : raw39923step0Labels = raw39923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39923 raw39923Labels permutation346 hz
    mixedMoment B raw39923step0 raw39923step0Labels = mixedMoment B raw39923step1 raw39923step1Labels := by
      have ha : raw39923step1 = (fun i j => raw39923step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39923step1 raw39923step0; decide +kernel
      have hl : raw39923step1Labels = raw39923step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39923step0 raw39923step0Labels permutation84 permutation6
    mixedMoment B raw39923step1 raw39923step1Labels = mixedMoment B raw39923step2 raw39923step2Labels := by
      have ha : raw39923step2 = -raw39923step1 := by apply Matrix.ext; change ∀ i j, raw39923step2 i j = -(raw39923step1 i j); unfold raw39923step2 raw39923step1; decide +kernel
      have hl : raw39923step2Labels = raw39923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node450 node450Labels := by rfl

def raw39924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39924Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39924step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw39924step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw39924step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39924 raw39924Labels = mixedMoment B node175 node175Labels := by
  calc
    mixedMoment B raw39924 raw39924Labels = mixedMoment B raw39924step0 raw39924step0Labels := by
      have hz : ∀ j, raw39924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39924step0 = (fun i j => raw39924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39924step0 raw39924; decide +kernel
      have hl : raw39924step0Labels = raw39924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39924 raw39924Labels permutation346 hz
    mixedMoment B raw39924step0 raw39924step0Labels = mixedMoment B raw39924step1 raw39924step1Labels := by
      have ha : raw39924step1 = (fun i j => raw39924step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39924step1 raw39924step0; decide +kernel
      have hl : raw39924step1Labels = raw39924step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39924step0 raw39924step0Labels permutation84 permutation6
    mixedMoment B raw39924step1 raw39924step1Labels = mixedMoment B raw39924step2 raw39924step2Labels := by
      have ha : raw39924step2 = -raw39924step1 := by apply Matrix.ext; change ∀ i j, raw39924step2 i j = -(raw39924step1 i j); unfold raw39924step2 raw39924step1; decide +kernel
      have hl : raw39924step2Labels = raw39924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node175 node175Labels := by rfl

def raw39925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39925Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39925step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39925 raw39925Labels = mixedMoment B node295 node295Labels := by
  calc
    mixedMoment B raw39925 raw39925Labels = mixedMoment B raw39925step0 raw39925step0Labels := by
      have ha : raw39925step0 = (fun i j => raw39925 (permutation539 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39925step0 raw39925; decide +kernel
      have hl : raw39925step0Labels = raw39925Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39925 raw39925Labels permutation539 permutation6
    _ = mixedMoment B node295 node295Labels := by rfl

def raw39926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw39926Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw39926step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw39926step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 2, -4]]
def raw39926step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw39926step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39926 raw39926Labels = mixedMoment B node160 node160Labels := by
  calc
    mixedMoment B raw39926 raw39926Labels = mixedMoment B raw39926step0 raw39926step0Labels := by
      have hz : ∀ j, raw39926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39926step0 = (fun i j => raw39926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39926step0 raw39926; decide +kernel
      have hl : raw39926step0Labels = raw39926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39926 raw39926Labels permutation434 hz
    mixedMoment B raw39926step0 raw39926step0Labels = mixedMoment B raw39926step1 raw39926step1Labels := by
      have hz : ∀ j, raw39926step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39926step1 = (fun i j => raw39926step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39926step1 raw39926step0; decide +kernel
      have hl : raw39926step1Labels = raw39926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39926step0 raw39926step0Labels permutation80 hz
    mixedMoment B raw39926step1 raw39926step1Labels = mixedMoment B raw39926step2 raw39926step2Labels := by
      have hz : ∀ j, raw39926step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39926step2 = (fun i j => raw39926step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39926step2 raw39926step1; decide +kernel
      have hl : raw39926step2Labels = raw39926step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39926step1 raw39926step1Labels permutation14 hz
    mixedMoment B raw39926step2 raw39926step2Labels = mixedMoment B raw39926step3 raw39926step3Labels := by
      have ha : raw39926step3 = (fun i j => raw39926step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39926step3 raw39926step2; decide +kernel
      have hl : raw39926step3Labels = raw39926step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39926step2 raw39926step2Labels permutation6 permutation6
    _ = mixedMoment B node160 node160Labels := by rfl

def raw39927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw39927Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw39927step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw39927step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 3, -5]]
def raw39927step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw39927step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39927 raw39927Labels = mixedMoment B node38 node38Labels := by
  calc
    mixedMoment B raw39927 raw39927Labels = mixedMoment B raw39927step0 raw39927step0Labels := by
      have hz : ∀ j, raw39927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39927step0 = (fun i j => raw39927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39927step0 raw39927; decide +kernel
      have hl : raw39927step0Labels = raw39927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39927 raw39927Labels permutation434 hz
    mixedMoment B raw39927step0 raw39927step0Labels = mixedMoment B raw39927step1 raw39927step1Labels := by
      have hz : ∀ j, raw39927step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39927step1 = (fun i j => raw39927step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39927step1 raw39927step0; decide +kernel
      have hl : raw39927step1Labels = raw39927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39927step0 raw39927step0Labels permutation80 hz
    mixedMoment B raw39927step1 raw39927step1Labels = mixedMoment B raw39927step2 raw39927step2Labels := by
      have hz : ∀ j, raw39927step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39927step2 = (fun i j => raw39927step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39927step2 raw39927step1; decide +kernel
      have hl : raw39927step2Labels = raw39927step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39927step1 raw39927step1Labels permutation14 hz
    mixedMoment B raw39927step2 raw39927step2Labels = mixedMoment B raw39927step3 raw39927step3Labels := by
      have ha : raw39927step3 = (fun i j => raw39927step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39927step3 raw39927step2; decide +kernel
      have hl : raw39927step3Labels = raw39927step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39927step2 raw39927step2Labels permutation6 permutation6
    _ = mixedMoment B node38 node38Labels := by rfl

def raw39928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw39928Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw39928step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw39928step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![1, -2, 1]]
def raw39928step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39928step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39928 raw39928Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39928 raw39928Labels = mixedMoment B raw39928step0 raw39928step0Labels := by
      have hz : ∀ j, raw39928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39928step0 = (fun i j => raw39928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39928step0 raw39928; decide +kernel
      have hl : raw39928step0Labels = raw39928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39928 raw39928Labels permutation434 hz
    mixedMoment B raw39928step0 raw39928step0Labels = mixedMoment B raw39928step1 raw39928step1Labels := by
      have hz : ∀ j, raw39928step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39928step1 = (fun i j => raw39928step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39928step1 raw39928step0; decide +kernel
      have hl : raw39928step1Labels = raw39928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39928step0 raw39928step0Labels permutation80 hz
    mixedMoment B raw39928step1 raw39928step1Labels = mixedMoment B raw39928step2 raw39928step2Labels := by
      have hz : ∀ j, raw39928step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39928step2 = (fun i j => raw39928step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39928step2 raw39928step1; decide +kernel
      have hl : raw39928step2Labels = raw39928step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39928step1 raw39928step1Labels permutation14 hz
    mixedMoment B raw39928step2 raw39928step2Labels = mixedMoment B raw39928step3 raw39928step3Labels := by
      have ha : raw39928step3 = (fun i j => raw39928step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39928step3 raw39928step2; decide +kernel
      have hl : raw39928step3Labels = raw39928step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39928step2 raw39928step2Labels permutation5 permutation6
    _ = mixedMoment B node420 node420Labels := by rfl

def raw39929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw39929Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw39929step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw39929step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39929step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39929 raw39929Labels = mixedMoment B node33 node33Labels := by
  calc
    mixedMoment B raw39929 raw39929Labels = mixedMoment B raw39929step0 raw39929step0Labels := by
      have hz : ∀ j, raw39929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39929step0 = (fun i j => raw39929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39929step0 raw39929; decide +kernel
      have hl : raw39929step0Labels = raw39929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39929 raw39929Labels permutation346 hz
    mixedMoment B raw39929step0 raw39929step0Labels = mixedMoment B raw39929step1 raw39929step1Labels := by
      have hz : ∀ j, raw39929step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39929step1 = (fun i j => raw39929step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39929step1 raw39929step0; decide +kernel
      have hl : raw39929step1Labels = raw39929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39929step0 raw39929step0Labels permutation56 hz
    mixedMoment B raw39929step1 raw39929step1Labels = mixedMoment B raw39929step2 raw39929step2Labels := by
      have ha : raw39929step2 = (fun i j => raw39929step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39929step2 raw39929step1; decide +kernel
      have hl : raw39929step2Labels = raw39929step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39929step1 raw39929step1Labels permutation28 permutation6
    _ = mixedMoment B node33 node33Labels := by rfl

def raw39930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw39930Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw39930step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw39930step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39930step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39930 raw39930Labels = mixedMoment B node111 node111Labels := by
  calc
    mixedMoment B raw39930 raw39930Labels = mixedMoment B raw39930step0 raw39930step0Labels := by
      have hz : ∀ j, raw39930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39930step0 = (fun i j => raw39930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39930step0 raw39930; decide +kernel
      have hl : raw39930step0Labels = raw39930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39930 raw39930Labels permutation346 hz
    mixedMoment B raw39930step0 raw39930step0Labels = mixedMoment B raw39930step1 raw39930step1Labels := by
      have hz : ∀ j, raw39930step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39930step1 = (fun i j => raw39930step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39930step1 raw39930step0; decide +kernel
      have hl : raw39930step1Labels = raw39930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39930step0 raw39930step0Labels permutation56 hz
    mixedMoment B raw39930step1 raw39930step1Labels = mixedMoment B raw39930step2 raw39930step2Labels := by
      have ha : raw39930step2 = (fun i j => raw39930step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39930step2 raw39930step1; decide +kernel
      have hl : raw39930step2Labels = raw39930step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39930step1 raw39930step1Labels permutation23 permutation6
    _ = mixedMoment B node111 node111Labels := by rfl

def raw39931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw39931Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw39931step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw39931step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39931step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39931 raw39931Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw39931 raw39931Labels = mixedMoment B raw39931step0 raw39931step0Labels := by
      have hz : ∀ j, raw39931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39931step0 = (fun i j => raw39931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39931step0 raw39931; decide +kernel
      have hl : raw39931step0Labels = raw39931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39931 raw39931Labels permutation346 hz
    mixedMoment B raw39931step0 raw39931step0Labels = mixedMoment B raw39931step1 raw39931step1Labels := by
      have hz : ∀ j, raw39931step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39931step1 = (fun i j => raw39931step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39931step1 raw39931step0; decide +kernel
      have hl : raw39931step1Labels = raw39931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39931step0 raw39931step0Labels permutation56 hz
    mixedMoment B raw39931step1 raw39931step1Labels = mixedMoment B raw39931step2 raw39931step2Labels := by
      have ha : raw39931step2 = (fun i j => raw39931step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39931step2 raw39931step1; decide +kernel
      have hl : raw39931step2Labels = raw39931step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39931step1 raw39931step1Labels permutation25 permutation6
    _ = mixedMoment B node405 node405Labels := by rfl

def raw39932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw39932Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw39932step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw39932step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39932step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39932 raw39932Labels = mixedMoment B node98 node98Labels := by
  calc
    mixedMoment B raw39932 raw39932Labels = mixedMoment B raw39932step0 raw39932step0Labels := by
      have hz : ∀ j, raw39932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39932step0 = (fun i j => raw39932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39932step0 raw39932; decide +kernel
      have hl : raw39932step0Labels = raw39932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39932 raw39932Labels permutation346 hz
    mixedMoment B raw39932step0 raw39932step0Labels = mixedMoment B raw39932step1 raw39932step1Labels := by
      have hz : ∀ j, raw39932step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39932step1 = (fun i j => raw39932step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39932step1 raw39932step0; decide +kernel
      have hl : raw39932step1Labels = raw39932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39932step0 raw39932step0Labels permutation56 hz
    mixedMoment B raw39932step1 raw39932step1Labels = mixedMoment B raw39932step2 raw39932step2Labels := by
      have ha : raw39932step2 = (fun i j => raw39932step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39932step2 raw39932step1; decide +kernel
      have hl : raw39932step2Labels = raw39932step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39932step1 raw39932step1Labels permutation24 permutation6
    _ = mixedMoment B node98 node98Labels := by rfl

def raw39933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39933Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39933step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39933step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39933step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39933 raw39933Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw39933 raw39933Labels = mixedMoment B raw39933step0 raw39933step0Labels := by
      have hz : ∀ j, raw39933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39933step0 = (fun i j => raw39933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39933step0 raw39933; decide +kernel
      have hl : raw39933step0Labels = raw39933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39933 raw39933Labels permutation346 hz
    mixedMoment B raw39933step0 raw39933step0Labels = mixedMoment B raw39933step1 raw39933step1Labels := by
      have hz : ∀ j, raw39933step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39933step1 = (fun i j => raw39933step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39933step1 raw39933step0; decide +kernel
      have hl : raw39933step1Labels = raw39933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39933step0 raw39933step0Labels permutation56 hz
    mixedMoment B raw39933step1 raw39933step1Labels = mixedMoment B raw39933step2 raw39933step2Labels := by
      have ha : raw39933step2 = (fun i j => raw39933step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39933step2 raw39933step1; decide +kernel
      have hl : raw39933step2Labels = raw39933step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39933step1 raw39933step1Labels permutation24 permutation6
    _ = mixedMoment B node343 node343Labels := by rfl

def raw39934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39934Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39934step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39934step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw39934step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39934step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39934 raw39934Labels = mixedMoment B node452 node452Labels := by
  calc
    mixedMoment B raw39934 raw39934Labels = mixedMoment B raw39934step0 raw39934step0Labels := by
      have hz : ∀ j, raw39934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39934step0 = (fun i j => raw39934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39934step0 raw39934; decide +kernel
      have hl : raw39934step0Labels = raw39934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39934 raw39934Labels permutation346 hz
    mixedMoment B raw39934step0 raw39934step0Labels = mixedMoment B raw39934step1 raw39934step1Labels := by
      have hz : ∀ j, raw39934step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39934step1 = (fun i j => raw39934step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39934step1 raw39934step0; decide +kernel
      have hl : raw39934step1Labels = raw39934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39934step0 raw39934step0Labels permutation56 hz
    mixedMoment B raw39934step1 raw39934step1Labels = mixedMoment B raw39934step2 raw39934step2Labels := by
      have ha : raw39934step2 = (fun i j => raw39934step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39934step2 raw39934step1; decide +kernel
      have hl : raw39934step2Labels = raw39934step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39934step1 raw39934step1Labels permutation14 permutation6
    mixedMoment B raw39934step2 raw39934step2Labels = mixedMoment B raw39934step3 raw39934step3Labels := by
      have ha : raw39934step3 = -raw39934step2 := by apply Matrix.ext; change ∀ i j, raw39934step3 i j = -(raw39934step2 i j); unfold raw39934step3 raw39934step2; decide +kernel
      have hl : raw39934step3Labels = raw39934step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node452 node452Labels := by rfl

def raw39935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw39935Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw39935step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw39935step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw39935step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39935 raw39935Labels = mixedMoment B node71 node71Labels := by
  calc
    mixedMoment B raw39935 raw39935Labels = mixedMoment B raw39935step0 raw39935step0Labels := by
      have hz : ∀ j, raw39935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39935step0 = (fun i j => raw39935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39935step0 raw39935; decide +kernel
      have hl : raw39935step0Labels = raw39935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39935 raw39935Labels permutation346 hz
    mixedMoment B raw39935step0 raw39935step0Labels = mixedMoment B raw39935step1 raw39935step1Labels := by
      have hz : ∀ j, raw39935step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39935step1 = (fun i j => raw39935step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39935step1 raw39935step0; decide +kernel
      have hl : raw39935step1Labels = raw39935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39935step0 raw39935step0Labels permutation56 hz
    mixedMoment B raw39935step1 raw39935step1Labels = mixedMoment B raw39935step2 raw39935step2Labels := by
      have ha : raw39935step2 = (fun i j => raw39935step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39935step2 raw39935step1; decide +kernel
      have hl : raw39935step2Labels = raw39935step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39935step1 raw39935step1Labels permutation24 permutation6
    _ = mixedMoment B node71 node71Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
