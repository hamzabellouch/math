import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28544 raw28544Labels = mixedMoment B node2453 node2453Labels := by
  calc
    mixedMoment B raw28544 raw28544Labels = mixedMoment B raw28544step0 raw28544step0Labels := by
      have ha : raw28544step0 = (fun i j => raw28544 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28544step0 raw28544; decide +kernel
      have hl : raw28544step0Labels = raw28544Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28544 raw28544Labels permutation682 permutation2
    mixedMoment B raw28544step0 raw28544step0Labels = mixedMoment B raw28544step1 raw28544step1Labels := by
      have ha : raw28544step1 = -raw28544step0 := by apply Matrix.ext; change ∀ i j, raw28544step1 i j = -(raw28544step0 i j); unfold raw28544step1 raw28544step0; decide +kernel
      have hl : raw28544step1Labels = raw28544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2453 node2453Labels := by rfl

def raw28545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw28545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28545 raw28545Labels = mixedMoment B node2455 node2455Labels := by
  calc
    mixedMoment B raw28545 raw28545Labels = mixedMoment B raw28545step0 raw28545step0Labels := by
      have ha : raw28545step0 = (fun i j => raw28545 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28545step0 raw28545; decide +kernel
      have hl : raw28545step0Labels = raw28545Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28545 raw28545Labels permutation682 permutation2
    mixedMoment B raw28545step0 raw28545step0Labels = mixedMoment B raw28545step1 raw28545step1Labels := by
      have ha : raw28545step1 = -raw28545step0 := by apply Matrix.ext; change ∀ i j, raw28545step1 i j = -(raw28545step0 i j); unfold raw28545step1 raw28545step0; decide +kernel
      have hl : raw28545step1Labels = raw28545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2455 node2455Labels := by rfl

def raw28546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28546 raw28546Labels = mixedMoment B node2490 node2490Labels := by
  calc
    mixedMoment B raw28546 raw28546Labels = mixedMoment B raw28546step0 raw28546step0Labels := by
      have ha : raw28546step0 = (fun i j => raw28546 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28546step0 raw28546; decide +kernel
      have hl : raw28546step0Labels = raw28546Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28546 raw28546Labels permutation688 permutation2
    mixedMoment B raw28546step0 raw28546step0Labels = mixedMoment B raw28546step1 raw28546step1Labels := by
      have ha : raw28546step1 = -raw28546step0 := by apply Matrix.ext; change ∀ i j, raw28546step1 i j = -(raw28546step0 i j); unfold raw28546step1 raw28546step0; decide +kernel
      have hl : raw28546step1Labels = raw28546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2490 node2490Labels := by rfl

def raw28547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw28547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28547 raw28547Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw28547 raw28547Labels = mixedMoment B raw28547step0 raw28547step0Labels := by
      have ha : raw28547step0 = (fun i j => raw28547 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28547step0 raw28547; decide +kernel
      have hl : raw28547step0Labels = raw28547Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28547 raw28547Labels permutation680 permutation2
    mixedMoment B raw28547step0 raw28547step0Labels = mixedMoment B raw28547step1 raw28547step1Labels := by
      have ha : raw28547step1 = -raw28547step0 := by apply Matrix.ext; change ∀ i j, raw28547step1 i j = -(raw28547step0 i j); unfold raw28547step1 raw28547step0; decide +kernel
      have hl : raw28547step1Labels = raw28547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw28548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28548 raw28548Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw28548 raw28548Labels = mixedMoment B raw28548step0 raw28548step0Labels := by
      have ha : raw28548step0 = (fun i j => raw28548 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28548step0 raw28548; decide +kernel
      have hl : raw28548step0Labels = raw28548Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28548 raw28548Labels permutation646 permutation2
    mixedMoment B raw28548step0 raw28548step0Labels = mixedMoment B raw28548step1 raw28548step1Labels := by
      have ha : raw28548step1 = -raw28548step0 := by apply Matrix.ext; change ∀ i j, raw28548step1 i j = -(raw28548step0 i j); unfold raw28548step1 raw28548step0; decide +kernel
      have hl : raw28548step1Labels = raw28548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw28549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28549 raw28549Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw28549 raw28549Labels = mixedMoment B raw28549step0 raw28549step0Labels := by
      have ha : raw28549step0 = (fun i j => raw28549 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28549step0 raw28549; decide +kernel
      have hl : raw28549step0Labels = raw28549Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28549 raw28549Labels permutation682 permutation2
    mixedMoment B raw28549step0 raw28549step0Labels = mixedMoment B raw28549step1 raw28549step1Labels := by
      have ha : raw28549step1 = -raw28549step0 := by apply Matrix.ext; change ∀ i j, raw28549step1 i j = -(raw28549step0 i j); unfold raw28549step1 raw28549step0; decide +kernel
      have hl : raw28549step1Labels = raw28549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw28550 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]
def raw28550Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28550step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]
def raw28550step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28550step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw28550step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28550 raw28550Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw28550 raw28550Labels = mixedMoment B raw28550step0 raw28550step0Labels := by
      have hz : ∀ j, raw28550 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw28550step0 = (fun i j => raw28550 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw28550step0 raw28550; decide +kernel
      have hl : raw28550step0Labels = raw28550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28550 raw28550Labels permutation265 hz
    mixedMoment B raw28550step0 raw28550step0Labels = mixedMoment B raw28550step1 raw28550step1Labels := by
      have ha : raw28550step1 = (fun i j => raw28550step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28550step1 raw28550step0; decide +kernel
      have hl : raw28550step1Labels = raw28550step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28550step0 raw28550step0Labels permutation38 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw28551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28551 raw28551Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw28551 raw28551Labels = mixedMoment B raw28551step0 raw28551step0Labels := by
      have hz : ∀ j, raw28551 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw28551step0 = (fun i j => raw28551 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw28551step0 raw28551; decide +kernel
      have hl : raw28551step0Labels = raw28551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28551 raw28551Labels permutation265 hz
    mixedMoment B raw28551step0 raw28551step0Labels = mixedMoment B raw28551step1 raw28551step1Labels := by
      have ha : raw28551step1 = (fun i j => raw28551step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28551step1 raw28551step0; decide +kernel
      have hl : raw28551step1Labels = raw28551step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28551step0 raw28551step0Labels permutation38 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw28552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28552 raw28552Labels = mixedMoment B node2536 node2536Labels := by
  calc
    mixedMoment B raw28552 raw28552Labels = mixedMoment B raw28552step0 raw28552step0Labels := by
      have ha : raw28552step0 = (fun i j => raw28552 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28552step0 raw28552; decide +kernel
      have hl : raw28552step0Labels = raw28552Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28552 raw28552Labels permutation158 permutation2
    _ = mixedMoment B node2536 node2536Labels := by rfl

def raw28553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28553 raw28553Labels = mixedMoment B node2565 node2565Labels := by
  calc
    _ = mixedMoment B node2565 node2565Labels := by rfl

def raw28554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw28554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28554 raw28554Labels = mixedMoment B node2533 node2533Labels := by
  calc
    mixedMoment B raw28554 raw28554Labels = mixedMoment B raw28554step0 raw28554step0Labels := by
      have ha : raw28554step0 = (fun i j => raw28554 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28554step0 raw28554; decide +kernel
      have hl : raw28554step0Labels = raw28554Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28554 raw28554Labels permutation158 permutation2
    _ = mixedMoment B node2533 node2533Labels := by rfl

def raw28555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28555 raw28555Labels = mixedMoment B node1991 node1991Labels := by
  calc
    mixedMoment B raw28555 raw28555Labels = mixedMoment B raw28555step0 raw28555step0Labels := by
      have ha : raw28555step0 = (fun i j => raw28555 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28555step0 raw28555; decide +kernel
      have hl : raw28555step0Labels = raw28555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28555 raw28555Labels permutation682 permutation2
    mixedMoment B raw28555step0 raw28555step0Labels = mixedMoment B raw28555step1 raw28555step1Labels := by
      have ha : raw28555step1 = -raw28555step0 := by apply Matrix.ext; change ∀ i j, raw28555step1 i j = -(raw28555step0 i j); unfold raw28555step1 raw28555step0; decide +kernel
      have hl : raw28555step1Labels = raw28555step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1991 node1991Labels := by rfl

def raw28556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw28556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28556 raw28556Labels = mixedMoment B node1993 node1993Labels := by
  calc
    mixedMoment B raw28556 raw28556Labels = mixedMoment B raw28556step0 raw28556step0Labels := by
      have ha : raw28556step0 = (fun i j => raw28556 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28556step0 raw28556; decide +kernel
      have hl : raw28556step0Labels = raw28556Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28556 raw28556Labels permutation682 permutation2
    mixedMoment B raw28556step0 raw28556step0Labels = mixedMoment B raw28556step1 raw28556step1Labels := by
      have ha : raw28556step1 = -raw28556step0 := by apply Matrix.ext; change ∀ i j, raw28556step1 i j = -(raw28556step0 i j); unfold raw28556step1 raw28556step0; decide +kernel
      have hl : raw28556step1Labels = raw28556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1993 node1993Labels := by rfl

def raw28557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28557 raw28557Labels = mixedMoment B node2030 node2030Labels := by
  calc
    mixedMoment B raw28557 raw28557Labels = mixedMoment B raw28557step0 raw28557step0Labels := by
      have ha : raw28557step0 = (fun i j => raw28557 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28557step0 raw28557; decide +kernel
      have hl : raw28557step0Labels = raw28557Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28557 raw28557Labels permutation688 permutation2
    mixedMoment B raw28557step0 raw28557step0Labels = mixedMoment B raw28557step1 raw28557step1Labels := by
      have ha : raw28557step1 = -raw28557step0 := by apply Matrix.ext; change ∀ i j, raw28557step1 i j = -(raw28557step0 i j); unfold raw28557step1 raw28557step0; decide +kernel
      have hl : raw28557step1Labels = raw28557step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2030 node2030Labels := by rfl

def raw28558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw28558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28558 raw28558Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw28558 raw28558Labels = mixedMoment B raw28558step0 raw28558step0Labels := by
      have ha : raw28558step0 = (fun i j => raw28558 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28558step0 raw28558; decide +kernel
      have hl : raw28558step0Labels = raw28558Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28558 raw28558Labels permutation680 permutation2
    mixedMoment B raw28558step0 raw28558step0Labels = mixedMoment B raw28558step1 raw28558step1Labels := by
      have ha : raw28558step1 = -raw28558step0 := by apply Matrix.ext; change ∀ i j, raw28558step1 i j = -(raw28558step0 i j); unfold raw28558step1 raw28558step0; decide +kernel
      have hl : raw28558step1Labels = raw28558step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1997 node1997Labels := by rfl

def raw28559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw28559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28559 raw28559Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw28559 raw28559Labels = mixedMoment B raw28559step0 raw28559step0Labels := by
      have hz : ∀ j, raw28559 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28559step0 = (fun i j => raw28559 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28559step0 raw28559; decide +kernel
      have hl : raw28559step0Labels = raw28559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28559 raw28559Labels permutation520 hz
    mixedMoment B raw28559step0 raw28559step0Labels = mixedMoment B raw28559step1 raw28559step1Labels := by
      have ha : raw28559step1 = (fun i j => raw28559step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28559step1 raw28559step0; decide +kernel
      have hl : raw28559step1Labels = raw28559step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28559step0 raw28559step0Labels permutation145 permutation2
    mixedMoment B raw28559step1 raw28559step1Labels = mixedMoment B raw28559step2 raw28559step2Labels := by
      have ha : raw28559step2 = -raw28559step1 := by apply Matrix.ext; change ∀ i j, raw28559step2 i j = -(raw28559step1 i j); unfold raw28559step2 raw28559step1; decide +kernel
      have hl : raw28559step2Labels = raw28559step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw28560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28560 raw28560Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw28560 raw28560Labels = mixedMoment B raw28560step0 raw28560step0Labels := by
      have ha : raw28560step0 = (fun i j => raw28560 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28560step0 raw28560; decide +kernel
      have hl : raw28560step0Labels = raw28560Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28560 raw28560Labels permutation682 permutation2
    mixedMoment B raw28560step0 raw28560step0Labels = mixedMoment B raw28560step1 raw28560step1Labels := by
      have ha : raw28560step1 = -raw28560step0 := by apply Matrix.ext; change ∀ i j, raw28560step1 i j = -(raw28560step0 i j); unfold raw28560step1 raw28560step0; decide +kernel
      have hl : raw28560step1Labels = raw28560step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw28561 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![0, 0], ![3, -3]]
def raw28561Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![3, -3]]
def raw28561step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw28561step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw28561step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw28561step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28561 raw28561Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw28561 raw28561Labels = mixedMoment B raw28561step0 raw28561step0Labels := by
      have hz : ∀ j, raw28561 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28561step0 = (fun i j => raw28561 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28561step0 raw28561; decide +kernel
      have hl : raw28561step0Labels = raw28561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28561 raw28561Labels permutation520 hz
    mixedMoment B raw28561step0 raw28561step0Labels = mixedMoment B raw28561step1 raw28561step1Labels := by
      have hz : ∀ j, raw28561step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw28561step1 = (fun i j => raw28561step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw28561step1 raw28561step0; decide +kernel
      have hl : raw28561step1Labels = raw28561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28561step0 raw28561step0Labels permutation56 hz
    mixedMoment B raw28561step1 raw28561step1Labels = mixedMoment B raw28561step2 raw28561step2Labels := by
      have ha : raw28561step2 = (fun i j => raw28561step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28561step2 raw28561step1; decide +kernel
      have hl : raw28561step2Labels = raw28561step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28561step1 raw28561step1Labels permutation28 permutation0
    mixedMoment B raw28561step2 raw28561step2Labels = mixedMoment B raw28561step3 raw28561step3Labels := by
      have ha : raw28561step3 = -raw28561step2 := by apply Matrix.ext; change ∀ i j, raw28561step3 i j = -(raw28561step2 i j); unfold raw28561step3 raw28561step2; decide +kernel
      have hl : raw28561step3Labels = raw28561step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw28562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28562step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28562 raw28562Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw28562 raw28562Labels = mixedMoment B raw28562step0 raw28562step0Labels := by
      have hz : ∀ j, raw28562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28562step0 = (fun i j => raw28562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28562step0 raw28562; decide +kernel
      have hl : raw28562step0Labels = raw28562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28562 raw28562Labels permutation434 hz
    mixedMoment B raw28562step0 raw28562step0Labels = mixedMoment B raw28562step1 raw28562step1Labels := by
      have hz : ∀ j, raw28562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28562step1 = (fun i j => raw28562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28562step1 raw28562step0; decide +kernel
      have hl : raw28562step1Labels = raw28562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28562step0 raw28562step0Labels permutation80 hz
    mixedMoment B raw28562step1 raw28562step1Labels = mixedMoment B raw28562step2 raw28562step2Labels := by
      have ha : raw28562step2 = (fun i j => raw28562step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28562step2 raw28562step1; decide +kernel
      have hl : raw28562step2Labels = raw28562step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28562step1 raw28562step1Labels permutation31 permutation2
    mixedMoment B raw28562step2 raw28562step2Labels = mixedMoment B raw28562step3 raw28562step3Labels := by
      have ha : raw28562step3 = -raw28562step2 := by apply Matrix.ext; change ∀ i j, raw28562step3 i j = -(raw28562step2 i j); unfold raw28562step3 raw28562step2; decide +kernel
      have hl : raw28562step3Labels = raw28562step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw28563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28563 raw28563Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw28563 raw28563Labels = mixedMoment B raw28563step0 raw28563step0Labels := by
      have hz : ∀ j, raw28563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28563step0 = (fun i j => raw28563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28563step0 raw28563; decide +kernel
      have hl : raw28563step0Labels = raw28563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28563 raw28563Labels permutation434 hz
    mixedMoment B raw28563step0 raw28563step0Labels = mixedMoment B raw28563step1 raw28563step1Labels := by
      have ha : raw28563step1 = (fun i j => raw28563step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28563step1 raw28563step0; decide +kernel
      have hl : raw28563step1Labels = raw28563step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28563step0 raw28563step0Labels permutation149 permutation2
    mixedMoment B raw28563step1 raw28563step1Labels = mixedMoment B raw28563step2 raw28563step2Labels := by
      have ha : raw28563step2 = -raw28563step1 := by apply Matrix.ext; change ∀ i j, raw28563step2 i j = -(raw28563step1 i j); unfold raw28563step2 raw28563step1; decide +kernel
      have hl : raw28563step2Labels = raw28563step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw28564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28564 raw28564Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw28564 raw28564Labels = mixedMoment B raw28564step0 raw28564step0Labels := by
      have hz : ∀ j, raw28564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28564step0 = (fun i j => raw28564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28564step0 raw28564; decide +kernel
      have hl : raw28564step0Labels = raw28564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28564 raw28564Labels permutation346 hz
    mixedMoment B raw28564step0 raw28564step0Labels = mixedMoment B raw28564step1 raw28564step1Labels := by
      have ha : raw28564step1 = (fun i j => raw28564step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28564step1 raw28564step0; decide +kernel
      have hl : raw28564step1Labels = raw28564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28564step0 raw28564step0Labels permutation149 permutation2
    mixedMoment B raw28564step1 raw28564step1Labels = mixedMoment B raw28564step2 raw28564step2Labels := by
      have ha : raw28564step2 = -raw28564step1 := by apply Matrix.ext; change ∀ i j, raw28564step2 i j = -(raw28564step1 i j); unfold raw28564step2 raw28564step1; decide +kernel
      have hl : raw28564step2Labels = raw28564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw28565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28565 raw28565Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw28565 raw28565Labels = mixedMoment B raw28565step0 raw28565step0Labels := by
      have hz : ∀ j, raw28565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28565step0 = (fun i j => raw28565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28565step0 raw28565; decide +kernel
      have hl : raw28565step0Labels = raw28565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28565 raw28565Labels permutation434 hz
    mixedMoment B raw28565step0 raw28565step0Labels = mixedMoment B raw28565step1 raw28565step1Labels := by
      have ha : raw28565step1 = (fun i j => raw28565step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28565step1 raw28565step0; decide +kernel
      have hl : raw28565step1Labels = raw28565step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28565step0 raw28565step0Labels permutation145 permutation2
    mixedMoment B raw28565step1 raw28565step1Labels = mixedMoment B raw28565step2 raw28565step2Labels := by
      have ha : raw28565step2 = -raw28565step1 := by apply Matrix.ext; change ∀ i j, raw28565step2 i j = -(raw28565step1 i j); unfold raw28565step2 raw28565step1; decide +kernel
      have hl : raw28565step2Labels = raw28565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4776 node4776Labels := by rfl

def raw28566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28566 raw28566Labels = mixedMoment B node4771 node4771Labels := by
  calc
    mixedMoment B raw28566 raw28566Labels = mixedMoment B raw28566step0 raw28566step0Labels := by
      have ha : raw28566step0 = (fun i j => raw28566 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28566step0 raw28566; decide +kernel
      have hl : raw28566step0Labels = raw28566Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28566 raw28566Labels permutation644 permutation2
    mixedMoment B raw28566step0 raw28566step0Labels = mixedMoment B raw28566step1 raw28566step1Labels := by
      have ha : raw28566step1 = -raw28566step0 := by apply Matrix.ext; change ∀ i j, raw28566step1 i j = -(raw28566step0 i j); unfold raw28566step1 raw28566step0; decide +kernel
      have hl : raw28566step1Labels = raw28566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4771 node4771Labels := by rfl

def raw28567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28567 raw28567Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw28567 raw28567Labels = mixedMoment B raw28567step0 raw28567step0Labels := by
      have hz : ∀ j, raw28567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28567step0 = (fun i j => raw28567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28567step0 raw28567; decide +kernel
      have hl : raw28567step0Labels = raw28567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28567 raw28567Labels permutation346 hz
    mixedMoment B raw28567step0 raw28567step0Labels = mixedMoment B raw28567step1 raw28567step1Labels := by
      have ha : raw28567step1 = (fun i j => raw28567step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28567step1 raw28567step0; decide +kernel
      have hl : raw28567step1Labels = raw28567step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28567step0 raw28567step0Labels permutation145 permutation2
    mixedMoment B raw28567step1 raw28567step1Labels = mixedMoment B raw28567step2 raw28567step2Labels := by
      have ha : raw28567step2 = -raw28567step1 := by apply Matrix.ext; change ∀ i j, raw28567step2 i j = -(raw28567step1 i j); unfold raw28567step2 raw28567step1; decide +kernel
      have hl : raw28567step2Labels = raw28567step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4776 node4776Labels := by rfl

def raw28568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28568 raw28568Labels = mixedMoment B node4771 node4771Labels := by
  calc
    mixedMoment B raw28568 raw28568Labels = mixedMoment B raw28568step0 raw28568step0Labels := by
      have ha : raw28568step0 = (fun i j => raw28568 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28568step0 raw28568; decide +kernel
      have hl : raw28568step0Labels = raw28568Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28568 raw28568Labels permutation662 permutation2
    mixedMoment B raw28568step0 raw28568step0Labels = mixedMoment B raw28568step1 raw28568step1Labels := by
      have ha : raw28568step1 = -raw28568step0 := by apply Matrix.ext; change ∀ i j, raw28568step1 i j = -(raw28568step0 i j); unfold raw28568step1 raw28568step0; decide +kernel
      have hl : raw28568step1Labels = raw28568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4771 node4771Labels := by rfl

def raw28569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28569 raw28569Labels = mixedMoment B node4704 node4704Labels := by
  calc
    mixedMoment B raw28569 raw28569Labels = mixedMoment B raw28569step0 raw28569step0Labels := by
      have hz : ∀ j, raw28569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28569step0 = (fun i j => raw28569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28569step0 raw28569; decide +kernel
      have hl : raw28569step0Labels = raw28569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28569 raw28569Labels permutation434 hz
    mixedMoment B raw28569step0 raw28569step0Labels = mixedMoment B raw28569step1 raw28569step1Labels := by
      have hz : ∀ j, raw28569step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28569step1 = (fun i j => raw28569step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28569step1 raw28569step0; decide +kernel
      have hl : raw28569step1Labels = raw28569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28569step0 raw28569step0Labels permutation80 hz
    mixedMoment B raw28569step1 raw28569step1Labels = mixedMoment B raw28569step2 raw28569step2Labels := by
      have ha : raw28569step2 = (fun i j => raw28569step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28569step2 raw28569step1; decide +kernel
      have hl : raw28569step2Labels = raw28569step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28569step1 raw28569step1Labels permutation31 permutation2
    mixedMoment B raw28569step2 raw28569step2Labels = mixedMoment B raw28569step3 raw28569step3Labels := by
      have ha : raw28569step3 = -raw28569step2 := by apply Matrix.ext; change ∀ i j, raw28569step3 i j = -(raw28569step2 i j); unfold raw28569step3 raw28569step2; decide +kernel
      have hl : raw28569step3Labels = raw28569step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4704 node4704Labels := by rfl

def raw28570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28570 raw28570Labels = mixedMoment B node4697 node4697Labels := by
  calc
    mixedMoment B raw28570 raw28570Labels = mixedMoment B raw28570step0 raw28570step0Labels := by
      have hz : ∀ j, raw28570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28570step0 = (fun i j => raw28570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28570step0 raw28570; decide +kernel
      have hl : raw28570step0Labels = raw28570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28570 raw28570Labels permutation434 hz
    mixedMoment B raw28570step0 raw28570step0Labels = mixedMoment B raw28570step1 raw28570step1Labels := by
      have ha : raw28570step1 = (fun i j => raw28570step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28570step1 raw28570step0; decide +kernel
      have hl : raw28570step1Labels = raw28570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28570step0 raw28570step0Labels permutation149 permutation2
    mixedMoment B raw28570step1 raw28570step1Labels = mixedMoment B raw28570step2 raw28570step2Labels := by
      have ha : raw28570step2 = -raw28570step1 := by apply Matrix.ext; change ∀ i j, raw28570step2 i j = -(raw28570step1 i j); unfold raw28570step2 raw28570step1; decide +kernel
      have hl : raw28570step2Labels = raw28570step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4697 node4697Labels := by rfl

def raw28571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28571 raw28571Labels = mixedMoment B node4697 node4697Labels := by
  calc
    mixedMoment B raw28571 raw28571Labels = mixedMoment B raw28571step0 raw28571step0Labels := by
      have hz : ∀ j, raw28571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28571step0 = (fun i j => raw28571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28571step0 raw28571; decide +kernel
      have hl : raw28571step0Labels = raw28571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28571 raw28571Labels permutation346 hz
    mixedMoment B raw28571step0 raw28571step0Labels = mixedMoment B raw28571step1 raw28571step1Labels := by
      have ha : raw28571step1 = (fun i j => raw28571step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28571step1 raw28571step0; decide +kernel
      have hl : raw28571step1Labels = raw28571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28571step0 raw28571step0Labels permutation149 permutation2
    mixedMoment B raw28571step1 raw28571step1Labels = mixedMoment B raw28571step2 raw28571step2Labels := by
      have ha : raw28571step2 = -raw28571step1 := by apply Matrix.ext; change ∀ i j, raw28571step2 i j = -(raw28571step1 i j); unfold raw28571step2 raw28571step1; decide +kernel
      have hl : raw28571step2Labels = raw28571step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4697 node4697Labels := by rfl

def raw28572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28572step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28572 raw28572Labels = mixedMoment B node4373 node4373Labels := by
  calc
    mixedMoment B raw28572 raw28572Labels = mixedMoment B raw28572step0 raw28572step0Labels := by
      have hz : ∀ j, raw28572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28572step0 = (fun i j => raw28572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28572step0 raw28572; decide +kernel
      have hl : raw28572step0Labels = raw28572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28572 raw28572Labels permutation434 hz
    mixedMoment B raw28572step0 raw28572step0Labels = mixedMoment B raw28572step1 raw28572step1Labels := by
      have hz : ∀ j, raw28572step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28572step1 = (fun i j => raw28572step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28572step1 raw28572step0; decide +kernel
      have hl : raw28572step1Labels = raw28572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28572step0 raw28572step0Labels permutation80 hz
    mixedMoment B raw28572step1 raw28572step1Labels = mixedMoment B raw28572step2 raw28572step2Labels := by
      have ha : raw28572step2 = (fun i j => raw28572step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28572step2 raw28572step1; decide +kernel
      have hl : raw28572step2Labels = raw28572step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28572step1 raw28572step1Labels permutation31 permutation2
    mixedMoment B raw28572step2 raw28572step2Labels = mixedMoment B raw28572step3 raw28572step3Labels := by
      have ha : raw28572step3 = -raw28572step2 := by apply Matrix.ext; change ∀ i j, raw28572step3 i j = -(raw28572step2 i j); unfold raw28572step3 raw28572step2; decide +kernel
      have hl : raw28572step3Labels = raw28572step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4373 node4373Labels := by rfl

def raw28573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28573 raw28573Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw28573 raw28573Labels = mixedMoment B raw28573step0 raw28573step0Labels := by
      have hz : ∀ j, raw28573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28573step0 = (fun i j => raw28573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28573step0 raw28573; decide +kernel
      have hl : raw28573step0Labels = raw28573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28573 raw28573Labels permutation434 hz
    mixedMoment B raw28573step0 raw28573step0Labels = mixedMoment B raw28573step1 raw28573step1Labels := by
      have ha : raw28573step1 = (fun i j => raw28573step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28573step1 raw28573step0; decide +kernel
      have hl : raw28573step1Labels = raw28573step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28573step0 raw28573step0Labels permutation149 permutation2
    mixedMoment B raw28573step1 raw28573step1Labels = mixedMoment B raw28573step2 raw28573step2Labels := by
      have ha : raw28573step2 = -raw28573step1 := by apply Matrix.ext; change ∀ i j, raw28573step2 i j = -(raw28573step1 i j); unfold raw28573step2 raw28573step1; decide +kernel
      have hl : raw28573step2Labels = raw28573step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4365 node4365Labels := by rfl

def raw28574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28574 raw28574Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw28574 raw28574Labels = mixedMoment B raw28574step0 raw28574step0Labels := by
      have hz : ∀ j, raw28574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28574step0 = (fun i j => raw28574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28574step0 raw28574; decide +kernel
      have hl : raw28574step0Labels = raw28574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28574 raw28574Labels permutation346 hz
    mixedMoment B raw28574step0 raw28574step0Labels = mixedMoment B raw28574step1 raw28574step1Labels := by
      have ha : raw28574step1 = (fun i j => raw28574step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28574step1 raw28574step0; decide +kernel
      have hl : raw28574step1Labels = raw28574step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28574step0 raw28574step0Labels permutation149 permutation2
    mixedMoment B raw28574step1 raw28574step1Labels = mixedMoment B raw28574step2 raw28574step2Labels := by
      have ha : raw28574step2 = -raw28574step1 := by apply Matrix.ext; change ∀ i j, raw28574step2 i j = -(raw28574step1 i j); unfold raw28574step2 raw28574step1; decide +kernel
      have hl : raw28574step2Labels = raw28574step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4365 node4365Labels := by rfl

def raw28575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28575step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28575step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28575step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw28575step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28575 raw28575Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw28575 raw28575Labels = mixedMoment B raw28575step0 raw28575step0Labels := by
      have hz : ∀ j, raw28575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28575step0 = (fun i j => raw28575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28575step0 raw28575; decide +kernel
      have hl : raw28575step0Labels = raw28575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28575 raw28575Labels permutation434 hz
    mixedMoment B raw28575step0 raw28575step0Labels = mixedMoment B raw28575step1 raw28575step1Labels := by
      have hz : ∀ j, raw28575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28575step1 = (fun i j => raw28575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28575step1 raw28575step0; decide +kernel
      have hl : raw28575step1Labels = raw28575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28575step0 raw28575step0Labels permutation80 hz
    mixedMoment B raw28575step1 raw28575step1Labels = mixedMoment B raw28575step2 raw28575step2Labels := by
      have ha : raw28575step2 = (fun i j => raw28575step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28575step2 raw28575step1; decide +kernel
      have hl : raw28575step2Labels = raw28575step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28575step1 raw28575step1Labels permutation30 permutation3
    mixedMoment B raw28575step2 raw28575step2Labels = mixedMoment B raw28575step3 raw28575step3Labels := by
      have ha : raw28575step3 = -raw28575step2 := by apply Matrix.ext; change ∀ i j, raw28575step3 i j = -(raw28575step2 i j); unfold raw28575step3 raw28575step2; decide +kernel
      have hl : raw28575step3Labels = raw28575step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3187 node3187Labels := by rfl

def raw28576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28576 raw28576Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw28576 raw28576Labels = mixedMoment B raw28576step0 raw28576step0Labels := by
      have hz : ∀ j, raw28576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28576step0 = (fun i j => raw28576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28576step0 raw28576; decide +kernel
      have hl : raw28576step0Labels = raw28576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28576 raw28576Labels permutation434 hz
    mixedMoment B raw28576step0 raw28576step0Labels = mixedMoment B raw28576step1 raw28576step1Labels := by
      have ha : raw28576step1 = (fun i j => raw28576step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28576step1 raw28576step0; decide +kernel
      have hl : raw28576step1Labels = raw28576step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28576step0 raw28576step0Labels permutation149 permutation3
    mixedMoment B raw28576step1 raw28576step1Labels = mixedMoment B raw28576step2 raw28576step2Labels := by
      have ha : raw28576step2 = -raw28576step1 := by apply Matrix.ext; change ∀ i j, raw28576step2 i j = -(raw28576step1 i j); unfold raw28576step2 raw28576step1; decide +kernel
      have hl : raw28576step2Labels = raw28576step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw28577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28577 raw28577Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw28577 raw28577Labels = mixedMoment B raw28577step0 raw28577step0Labels := by
      have hz : ∀ j, raw28577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28577step0 = (fun i j => raw28577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28577step0 raw28577; decide +kernel
      have hl : raw28577step0Labels = raw28577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28577 raw28577Labels permutation346 hz
    mixedMoment B raw28577step0 raw28577step0Labels = mixedMoment B raw28577step1 raw28577step1Labels := by
      have ha : raw28577step1 = (fun i j => raw28577step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28577step1 raw28577step0; decide +kernel
      have hl : raw28577step1Labels = raw28577step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28577step0 raw28577step0Labels permutation149 permutation3
    mixedMoment B raw28577step1 raw28577step1Labels = mixedMoment B raw28577step2 raw28577step2Labels := by
      have ha : raw28577step2 = -raw28577step1 := by apply Matrix.ext; change ∀ i j, raw28577step2 i j = -(raw28577step1 i j); unfold raw28577step2 raw28577step1; decide +kernel
      have hl : raw28577step2Labels = raw28577step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw28578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28578step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw28578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28578 raw28578Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw28578 raw28578Labels = mixedMoment B raw28578step0 raw28578step0Labels := by
      have hz : ∀ j, raw28578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28578step0 = (fun i j => raw28578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28578step0 raw28578; decide +kernel
      have hl : raw28578step0Labels = raw28578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28578 raw28578Labels permutation434 hz
    mixedMoment B raw28578step0 raw28578step0Labels = mixedMoment B raw28578step1 raw28578step1Labels := by
      have hz : ∀ j, raw28578step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28578step1 = (fun i j => raw28578step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28578step1 raw28578step0; decide +kernel
      have hl : raw28578step1Labels = raw28578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28578step0 raw28578step0Labels permutation80 hz
    mixedMoment B raw28578step1 raw28578step1Labels = mixedMoment B raw28578step2 raw28578step2Labels := by
      have ha : raw28578step2 = (fun i j => raw28578step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28578step2 raw28578step1; decide +kernel
      have hl : raw28578step2Labels = raw28578step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28578step1 raw28578step1Labels permutation31 permutation3
    mixedMoment B raw28578step2 raw28578step2Labels = mixedMoment B raw28578step3 raw28578step3Labels := by
      have ha : raw28578step3 = -raw28578step2 := by apply Matrix.ext; change ∀ i j, raw28578step3 i j = -(raw28578step2 i j); unfold raw28578step3 raw28578step2; decide +kernel
      have hl : raw28578step3Labels = raw28578step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw28579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28579 raw28579Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw28579 raw28579Labels = mixedMoment B raw28579step0 raw28579step0Labels := by
      have hz : ∀ j, raw28579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28579step0 = (fun i j => raw28579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28579step0 raw28579; decide +kernel
      have hl : raw28579step0Labels = raw28579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28579 raw28579Labels permutation434 hz
    mixedMoment B raw28579step0 raw28579step0Labels = mixedMoment B raw28579step1 raw28579step1Labels := by
      have ha : raw28579step1 = (fun i j => raw28579step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28579step1 raw28579step0; decide +kernel
      have hl : raw28579step1Labels = raw28579step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28579step0 raw28579step0Labels permutation32 permutation3
    _ = mixedMoment B node2816 node2816Labels := by rfl

def raw28580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28580 raw28580Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw28580 raw28580Labels = mixedMoment B raw28580step0 raw28580step0Labels := by
      have ha : raw28580step0 = (fun i j => raw28580 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28580step0 raw28580; decide +kernel
      have hl : raw28580step0Labels = raw28580Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28580 raw28580Labels permutation158 permutation3
    _ = mixedMoment B node2895 node2895Labels := by rfl

def raw28581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28581 raw28581Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw28581 raw28581Labels = mixedMoment B raw28581step0 raw28581step0Labels := by
      have hz : ∀ j, raw28581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28581step0 = (fun i j => raw28581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28581step0 raw28581; decide +kernel
      have hl : raw28581step0Labels = raw28581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28581 raw28581Labels permutation434 hz
    mixedMoment B raw28581step0 raw28581step0Labels = mixedMoment B raw28581step1 raw28581step1Labels := by
      have ha : raw28581step1 = (fun i j => raw28581step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28581step1 raw28581step0; decide +kernel
      have hl : raw28581step1Labels = raw28581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28581step0 raw28581step0Labels permutation34 permutation3
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw28582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28582 raw28582Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw28582 raw28582Labels = mixedMoment B raw28582step0 raw28582step0Labels := by
      have hz : ∀ j, raw28582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28582step0 = (fun i j => raw28582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28582step0 raw28582; decide +kernel
      have hl : raw28582step0Labels = raw28582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28582 raw28582Labels permutation346 hz
    mixedMoment B raw28582step0 raw28582step0Labels = mixedMoment B raw28582step1 raw28582step1Labels := by
      have ha : raw28582step1 = (fun i j => raw28582step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28582step1 raw28582step0; decide +kernel
      have hl : raw28582step1Labels = raw28582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28582step0 raw28582step0Labels permutation32 permutation3
    _ = mixedMoment B node2816 node2816Labels := by rfl

def raw28583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28583 raw28583Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw28583 raw28583Labels = mixedMoment B raw28583step0 raw28583step0Labels := by
      have ha : raw28583step0 = (fun i j => raw28583 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28583step0 raw28583; decide +kernel
      have hl : raw28583step0Labels = raw28583Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28583 raw28583Labels permutation152 permutation3
    _ = mixedMoment B node2895 node2895Labels := by rfl

def raw28584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28584 raw28584Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw28584 raw28584Labels = mixedMoment B raw28584step0 raw28584step0Labels := by
      have hz : ∀ j, raw28584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28584step0 = (fun i j => raw28584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28584step0 raw28584; decide +kernel
      have hl : raw28584step0Labels = raw28584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28584 raw28584Labels permutation346 hz
    mixedMoment B raw28584step0 raw28584step0Labels = mixedMoment B raw28584step1 raw28584step1Labels := by
      have ha : raw28584step1 = (fun i j => raw28584step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28584step1 raw28584step0; decide +kernel
      have hl : raw28584step1Labels = raw28584step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28584step0 raw28584step0Labels permutation34 permutation3
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw28585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28585step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw28585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28585 raw28585Labels = mixedMoment B node2821 node2821Labels := by
  calc
    mixedMoment B raw28585 raw28585Labels = mixedMoment B raw28585step0 raw28585step0Labels := by
      have hz : ∀ j, raw28585 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28585step0 = (fun i j => raw28585 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28585step0 raw28585; decide +kernel
      have hl : raw28585step0Labels = raw28585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28585 raw28585Labels permutation434 hz
    mixedMoment B raw28585step0 raw28585step0Labels = mixedMoment B raw28585step1 raw28585step1Labels := by
      have hz : ∀ j, raw28585step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28585step1 = (fun i j => raw28585step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28585step1 raw28585step0; decide +kernel
      have hl : raw28585step1Labels = raw28585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28585step0 raw28585step0Labels permutation80 hz
    mixedMoment B raw28585step1 raw28585step1Labels = mixedMoment B raw28585step2 raw28585step2Labels := by
      have ha : raw28585step2 = (fun i j => raw28585step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28585step2 raw28585step1; decide +kernel
      have hl : raw28585step2Labels = raw28585step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28585step1 raw28585step1Labels permutation8 permutation3
    _ = mixedMoment B node2821 node2821Labels := by rfl

def raw28586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw28586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28586 raw28586Labels = mixedMoment B node2899 node2899Labels := by
  calc
    mixedMoment B raw28586 raw28586Labels = mixedMoment B raw28586step0 raw28586step0Labels := by
      have hz : ∀ j, raw28586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28586step0 = (fun i j => raw28586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28586step0 raw28586; decide +kernel
      have hl : raw28586step0Labels = raw28586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28586 raw28586Labels permutation434 hz
    mixedMoment B raw28586step0 raw28586step0Labels = mixedMoment B raw28586step1 raw28586step1Labels := by
      have ha : raw28586step1 = (fun i j => raw28586step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28586step1 raw28586step0; decide +kernel
      have hl : raw28586step1Labels = raw28586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28586step0 raw28586step0Labels permutation32 permutation3
    _ = mixedMoment B node2899 node2899Labels := by rfl

def raw28587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw28587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28587 raw28587Labels = mixedMoment B node2899 node2899Labels := by
  calc
    mixedMoment B raw28587 raw28587Labels = mixedMoment B raw28587step0 raw28587step0Labels := by
      have hz : ∀ j, raw28587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28587step0 = (fun i j => raw28587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28587step0 raw28587; decide +kernel
      have hl : raw28587step0Labels = raw28587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28587 raw28587Labels permutation346 hz
    mixedMoment B raw28587step0 raw28587step0Labels = mixedMoment B raw28587step1 raw28587step1Labels := by
      have ha : raw28587step1 = (fun i j => raw28587step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28587step1 raw28587step0; decide +kernel
      have hl : raw28587step1Labels = raw28587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28587step0 raw28587step0Labels permutation32 permutation3
    _ = mixedMoment B node2899 node2899Labels := by rfl

def raw28588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 0, 2], ![-3, 2, 1]]
def raw28588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw28588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28588 raw28588Labels = mixedMoment B node1325 node1325Labels := by
  calc
    mixedMoment B raw28588 raw28588Labels = mixedMoment B raw28588step0 raw28588step0Labels := by
      have hz : ∀ j, raw28588 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28588step0 = (fun i j => raw28588 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28588step0 raw28588; decide +kernel
      have hl : raw28588step0Labels = raw28588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28588 raw28588Labels permutation434 hz
    mixedMoment B raw28588step0 raw28588step0Labels = mixedMoment B raw28588step1 raw28588step1Labels := by
      have hz : ∀ j, raw28588step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28588step1 = (fun i j => raw28588step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28588step1 raw28588step0; decide +kernel
      have hl : raw28588step1Labels = raw28588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28588step0 raw28588step0Labels permutation80 hz
    mixedMoment B raw28588step1 raw28588step1Labels = mixedMoment B raw28588step2 raw28588step2Labels := by
      have ha : raw28588step2 = (fun i j => raw28588step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28588step2 raw28588step1; decide +kernel
      have hl : raw28588step2Labels = raw28588step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28588step1 raw28588step1Labels permutation31 permutation3
    mixedMoment B raw28588step2 raw28588step2Labels = mixedMoment B raw28588step3 raw28588step3Labels := by
      have ha : raw28588step3 = -raw28588step2 := by apply Matrix.ext; change ∀ i j, raw28588step3 i j = -(raw28588step2 i j); unfold raw28588step3 raw28588step2; decide +kernel
      have hl : raw28588step3Labels = raw28588step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1325 node1325Labels := by rfl

def raw28589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28589 raw28589Labels = mixedMoment B node1320 node1320Labels := by
  calc
    mixedMoment B raw28589 raw28589Labels = mixedMoment B raw28589step0 raw28589step0Labels := by
      have hz : ∀ j, raw28589 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28589step0 = (fun i j => raw28589 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28589step0 raw28589; decide +kernel
      have hl : raw28589step0Labels = raw28589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28589 raw28589Labels permutation434 hz
    mixedMoment B raw28589step0 raw28589step0Labels = mixedMoment B raw28589step1 raw28589step1Labels := by
      have ha : raw28589step1 = (fun i j => raw28589step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28589step1 raw28589step0; decide +kernel
      have hl : raw28589step1Labels = raw28589step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28589step0 raw28589step0Labels permutation149 permutation3
    mixedMoment B raw28589step1 raw28589step1Labels = mixedMoment B raw28589step2 raw28589step2Labels := by
      have ha : raw28589step2 = -raw28589step1 := by apply Matrix.ext; change ∀ i j, raw28589step2 i j = -(raw28589step1 i j); unfold raw28589step2 raw28589step1; decide +kernel
      have hl : raw28589step2Labels = raw28589step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1320 node1320Labels := by rfl

def raw28590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28590 raw28590Labels = mixedMoment B node1320 node1320Labels := by
  calc
    mixedMoment B raw28590 raw28590Labels = mixedMoment B raw28590step0 raw28590step0Labels := by
      have hz : ∀ j, raw28590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28590step0 = (fun i j => raw28590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28590step0 raw28590; decide +kernel
      have hl : raw28590step0Labels = raw28590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28590 raw28590Labels permutation346 hz
    mixedMoment B raw28590step0 raw28590step0Labels = mixedMoment B raw28590step1 raw28590step1Labels := by
      have ha : raw28590step1 = (fun i j => raw28590step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28590step1 raw28590step0; decide +kernel
      have hl : raw28590step1Labels = raw28590step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28590step0 raw28590step0Labels permutation149 permutation3
    mixedMoment B raw28590step1 raw28590step1Labels = mixedMoment B raw28590step2 raw28590step2Labels := by
      have ha : raw28590step2 = -raw28590step1 := by apply Matrix.ext; change ∀ i j, raw28590step2 i j = -(raw28590step1 i j); unfold raw28590step2 raw28590step1; decide +kernel
      have hl : raw28590step2Labels = raw28590step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1320 node1320Labels := by rfl

def raw28591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28591step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28591step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28591step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28591step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28591 raw28591Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw28591 raw28591Labels = mixedMoment B raw28591step0 raw28591step0Labels := by
      have hz : ∀ j, raw28591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28591step0 = (fun i j => raw28591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28591step0 raw28591; decide +kernel
      have hl : raw28591step0Labels = raw28591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28591 raw28591Labels permutation434 hz
    mixedMoment B raw28591step0 raw28591step0Labels = mixedMoment B raw28591step1 raw28591step1Labels := by
      have hz : ∀ j, raw28591step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28591step1 = (fun i j => raw28591step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28591step1 raw28591step0; decide +kernel
      have hl : raw28591step1Labels = raw28591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28591step0 raw28591step0Labels permutation80 hz
    mixedMoment B raw28591step1 raw28591step1Labels = mixedMoment B raw28591step2 raw28591step2Labels := by
      have ha : raw28591step2 = (fun i j => raw28591step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28591step2 raw28591step1; decide +kernel
      have hl : raw28591step2Labels = raw28591step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28591step1 raw28591step1Labels permutation29 permutation7
    mixedMoment B raw28591step2 raw28591step2Labels = mixedMoment B raw28591step3 raw28591step3Labels := by
      have ha : raw28591step3 = raw28591step2 := by apply Matrix.ext; unfold raw28591step3 raw28591step2; decide +kernel
      have hl : raw28591step2Labels = labelEmbedding1 ∘ raw28591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28591step2 raw28591step2Labels raw28591step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw28592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28592 raw28592Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw28592 raw28592Labels = mixedMoment B raw28592step0 raw28592step0Labels := by
      have hz : ∀ j, raw28592 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28592step0 = (fun i j => raw28592 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28592step0 raw28592; decide +kernel
      have hl : raw28592step0Labels = raw28592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28592 raw28592Labels permutation434 hz
    mixedMoment B raw28592step0 raw28592step0Labels = mixedMoment B raw28592step1 raw28592step1Labels := by
      have ha : raw28592step1 = (fun i j => raw28592step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28592step1 raw28592step0; decide +kernel
      have hl : raw28592step1Labels = raw28592step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28592step0 raw28592step0Labels permutation137 permutation7
    mixedMoment B raw28592step1 raw28592step1Labels = mixedMoment B raw28592step2 raw28592step2Labels := by
      have ha : raw28592step2 = raw28592step1 := by apply Matrix.ext; unfold raw28592step2 raw28592step1; decide +kernel
      have hl : raw28592step1Labels = labelEmbedding1 ∘ raw28592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28592step1 raw28592step1Labels raw28592step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw28593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28593 raw28593Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw28593 raw28593Labels = mixedMoment B raw28593step0 raw28593step0Labels := by
      have hz : ∀ j, raw28593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28593step0 = (fun i j => raw28593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28593step0 raw28593; decide +kernel
      have hl : raw28593step0Labels = raw28593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28593 raw28593Labels permutation346 hz
    mixedMoment B raw28593step0 raw28593step0Labels = mixedMoment B raw28593step1 raw28593step1Labels := by
      have ha : raw28593step1 = (fun i j => raw28593step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28593step1 raw28593step0; decide +kernel
      have hl : raw28593step1Labels = raw28593step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28593step0 raw28593step0Labels permutation137 permutation7
    mixedMoment B raw28593step1 raw28593step1Labels = mixedMoment B raw28593step2 raw28593step2Labels := by
      have ha : raw28593step2 = raw28593step1 := by apply Matrix.ext; unfold raw28593step2 raw28593step1; decide +kernel
      have hl : raw28593step1Labels = labelEmbedding1 ∘ raw28593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28593step1 raw28593step1Labels raw28593step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw28594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28594step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28594 raw28594Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw28594 raw28594Labels = mixedMoment B raw28594step0 raw28594step0Labels := by
      have hz : ∀ j, raw28594 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28594step0 = (fun i j => raw28594 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28594step0 raw28594; decide +kernel
      have hl : raw28594step0Labels = raw28594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28594 raw28594Labels permutation434 hz
    mixedMoment B raw28594step0 raw28594step0Labels = mixedMoment B raw28594step1 raw28594step1Labels := by
      have ha : raw28594step1 = (fun i j => raw28594step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28594step1 raw28594step0; decide +kernel
      have hl : raw28594step1Labels = raw28594step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28594step0 raw28594step0Labels permutation143 permutation7
    mixedMoment B raw28594step1 raw28594step1Labels = mixedMoment B raw28594step2 raw28594step2Labels := by
      have ha : raw28594step2 = raw28594step1 := by apply Matrix.ext; unfold raw28594step2 raw28594step1; decide +kernel
      have hl : raw28594step1Labels = labelEmbedding1 ∘ raw28594step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28594step1 raw28594step1Labels raw28594step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

def raw28595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28595step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28595 raw28595Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw28595 raw28595Labels = mixedMoment B raw28595step0 raw28595step0Labels := by
      have ha : raw28595step0 = (fun i j => raw28595 (permutation632 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28595step0 raw28595; decide +kernel
      have hl : raw28595step0Labels = raw28595Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28595 raw28595Labels permutation632 permutation7
    mixedMoment B raw28595step0 raw28595step0Labels = mixedMoment B raw28595step1 raw28595step1Labels := by
      have ha : raw28595step1 = raw28595step0 := by apply Matrix.ext; unfold raw28595step1 raw28595step0; decide +kernel
      have hl : raw28595step0Labels = labelEmbedding1 ∘ raw28595step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28595step0 raw28595step0Labels raw28595step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

def raw28596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28596 raw28596Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw28596 raw28596Labels = mixedMoment B raw28596step0 raw28596step0Labels := by
      have hz : ∀ j, raw28596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28596step0 = (fun i j => raw28596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28596step0 raw28596; decide +kernel
      have hl : raw28596step0Labels = raw28596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28596 raw28596Labels permutation346 hz
    mixedMoment B raw28596step0 raw28596step0Labels = mixedMoment B raw28596step1 raw28596step1Labels := by
      have ha : raw28596step1 = (fun i j => raw28596step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28596step1 raw28596step0; decide +kernel
      have hl : raw28596step1Labels = raw28596step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28596step0 raw28596step0Labels permutation143 permutation7
    mixedMoment B raw28596step1 raw28596step1Labels = mixedMoment B raw28596step2 raw28596step2Labels := by
      have ha : raw28596step2 = raw28596step1 := by apply Matrix.ext; unfold raw28596step2 raw28596step1; decide +kernel
      have hl : raw28596step1Labels = labelEmbedding1 ∘ raw28596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28596step1 raw28596step1Labels raw28596step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

def raw28597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28597step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28597 raw28597Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw28597 raw28597Labels = mixedMoment B raw28597step0 raw28597step0Labels := by
      have ha : raw28597step0 = (fun i j => raw28597 (permutation653 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28597step0 raw28597; decide +kernel
      have hl : raw28597step0Labels = raw28597Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28597 raw28597Labels permutation653 permutation7
    mixedMoment B raw28597step0 raw28597step0Labels = mixedMoment B raw28597step1 raw28597step1Labels := by
      have ha : raw28597step1 = raw28597step0 := by apply Matrix.ext; unfold raw28597step1 raw28597step0; decide +kernel
      have hl : raw28597step0Labels = labelEmbedding1 ∘ raw28597step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28597step0 raw28597step0Labels raw28597step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

def raw28598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28598step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28598step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw28598step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28598step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw28598step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28598 raw28598Labels = mixedMoment B node2273 node2273Labels := by
  calc
    mixedMoment B raw28598 raw28598Labels = mixedMoment B raw28598step0 raw28598step0Labels := by
      have hz : ∀ j, raw28598 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28598step0 = (fun i j => raw28598 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28598step0 raw28598; decide +kernel
      have hl : raw28598step0Labels = raw28598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28598 raw28598Labels permutation434 hz
    mixedMoment B raw28598step0 raw28598step0Labels = mixedMoment B raw28598step1 raw28598step1Labels := by
      have hz : ∀ j, raw28598step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28598step1 = (fun i j => raw28598step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28598step1 raw28598step0; decide +kernel
      have hl : raw28598step1Labels = raw28598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28598step0 raw28598step0Labels permutation80 hz
    mixedMoment B raw28598step1 raw28598step1Labels = mixedMoment B raw28598step2 raw28598step2Labels := by
      have ha : raw28598step2 = (fun i j => raw28598step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28598step2 raw28598step1; decide +kernel
      have hl : raw28598step2Labels = raw28598step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28598step1 raw28598step1Labels permutation29 permutation7
    mixedMoment B raw28598step2 raw28598step2Labels = mixedMoment B raw28598step3 raw28598step3Labels := by
      have ha : raw28598step3 = raw28598step2 := by apply Matrix.ext; unfold raw28598step3 raw28598step2; decide +kernel
      have hl : raw28598step2Labels = labelEmbedding1 ∘ raw28598step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28598step2 raw28598step2Labels raw28598step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2273 node2273Labels := by rfl

def raw28599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28599 raw28599Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw28599 raw28599Labels = mixedMoment B raw28599step0 raw28599step0Labels := by
      have hz : ∀ j, raw28599 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28599step0 = (fun i j => raw28599 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28599step0 raw28599; decide +kernel
      have hl : raw28599step0Labels = raw28599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28599 raw28599Labels permutation434 hz
    mixedMoment B raw28599step0 raw28599step0Labels = mixedMoment B raw28599step1 raw28599step1Labels := by
      have ha : raw28599step1 = (fun i j => raw28599step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28599step1 raw28599step0; decide +kernel
      have hl : raw28599step1Labels = raw28599step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28599step0 raw28599step0Labels permutation137 permutation7
    mixedMoment B raw28599step1 raw28599step1Labels = mixedMoment B raw28599step2 raw28599step2Labels := by
      have ha : raw28599step2 = raw28599step1 := by apply Matrix.ext; unfold raw28599step2 raw28599step1; decide +kernel
      have hl : raw28599step1Labels = labelEmbedding1 ∘ raw28599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28599step1 raw28599step1Labels raw28599step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2239 node2239Labels := by rfl

def raw28600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28600 raw28600Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw28600 raw28600Labels = mixedMoment B raw28600step0 raw28600step0Labels := by
      have hz : ∀ j, raw28600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28600step0 = (fun i j => raw28600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28600step0 raw28600; decide +kernel
      have hl : raw28600step0Labels = raw28600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28600 raw28600Labels permutation346 hz
    mixedMoment B raw28600step0 raw28600step0Labels = mixedMoment B raw28600step1 raw28600step1Labels := by
      have ha : raw28600step1 = (fun i j => raw28600step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28600step1 raw28600step0; decide +kernel
      have hl : raw28600step1Labels = raw28600step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28600step0 raw28600step0Labels permutation137 permutation7
    mixedMoment B raw28600step1 raw28600step1Labels = mixedMoment B raw28600step2 raw28600step2Labels := by
      have ha : raw28600step2 = raw28600step1 := by apply Matrix.ext; unfold raw28600step2 raw28600step1; decide +kernel
      have hl : raw28600step1Labels = labelEmbedding1 ∘ raw28600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28600step1 raw28600step1Labels raw28600step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2239 node2239Labels := by rfl

def raw28601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28601step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28601 raw28601Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw28601 raw28601Labels = mixedMoment B raw28601step0 raw28601step0Labels := by
      have hz : ∀ j, raw28601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28601step0 = (fun i j => raw28601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28601step0 raw28601; decide +kernel
      have hl : raw28601step0Labels = raw28601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28601 raw28601Labels permutation434 hz
    mixedMoment B raw28601step0 raw28601step0Labels = mixedMoment B raw28601step1 raw28601step1Labels := by
      have hz : ∀ j, raw28601step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28601step1 = (fun i j => raw28601step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28601step1 raw28601step0; decide +kernel
      have hl : raw28601step1Labels = raw28601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28601step0 raw28601step0Labels permutation80 hz
    mixedMoment B raw28601step1 raw28601step1Labels = mixedMoment B raw28601step2 raw28601step2Labels := by
      have ha : raw28601step2 = (fun i j => raw28601step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28601step2 raw28601step1; decide +kernel
      have hl : raw28601step2Labels = raw28601step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28601step1 raw28601step1Labels permutation29 permutation7
    mixedMoment B raw28601step2 raw28601step2Labels = mixedMoment B raw28601step3 raw28601step3Labels := by
      have ha : raw28601step3 = raw28601step2 := by apply Matrix.ext; unfold raw28601step3 raw28601step2; decide +kernel
      have hl : raw28601step2Labels = labelEmbedding1 ∘ raw28601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28601step2 raw28601step2Labels raw28601step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

def raw28602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28602step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28602 raw28602Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw28602 raw28602Labels = mixedMoment B raw28602step0 raw28602step0Labels := by
      have hz : ∀ j, raw28602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28602step0 = (fun i j => raw28602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28602step0 raw28602; decide +kernel
      have hl : raw28602step0Labels = raw28602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28602 raw28602Labels permutation434 hz
    mixedMoment B raw28602step0 raw28602step0Labels = mixedMoment B raw28602step1 raw28602step1Labels := by
      have ha : raw28602step1 = (fun i j => raw28602step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28602step1 raw28602step0; decide +kernel
      have hl : raw28602step1Labels = raw28602step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28602step0 raw28602step0Labels permutation137 permutation7
    mixedMoment B raw28602step1 raw28602step1Labels = mixedMoment B raw28602step2 raw28602step2Labels := by
      have ha : raw28602step2 = raw28602step1 := by apply Matrix.ext; unfold raw28602step2 raw28602step1; decide +kernel
      have hl : raw28602step1Labels = labelEmbedding1 ∘ raw28602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28602step1 raw28602step1Labels raw28602step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

def raw28603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28603step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28603 raw28603Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw28603 raw28603Labels = mixedMoment B raw28603step0 raw28603step0Labels := by
      have hz : ∀ j, raw28603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28603step0 = (fun i j => raw28603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28603step0 raw28603; decide +kernel
      have hl : raw28603step0Labels = raw28603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28603 raw28603Labels permutation346 hz
    mixedMoment B raw28603step0 raw28603step0Labels = mixedMoment B raw28603step1 raw28603step1Labels := by
      have ha : raw28603step1 = (fun i j => raw28603step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28603step1 raw28603step0; decide +kernel
      have hl : raw28603step1Labels = raw28603step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28603step0 raw28603step0Labels permutation137 permutation7
    mixedMoment B raw28603step1 raw28603step1Labels = mixedMoment B raw28603step2 raw28603step2Labels := by
      have ha : raw28603step2 = raw28603step1 := by apply Matrix.ext; unfold raw28603step2 raw28603step1; decide +kernel
      have hl : raw28603step1Labels = labelEmbedding1 ∘ raw28603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28603step1 raw28603step1Labels raw28603step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

def raw28604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28604step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28604 raw28604Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw28604 raw28604Labels = mixedMoment B raw28604step0 raw28604step0Labels := by
      have hz : ∀ j, raw28604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28604step0 = (fun i j => raw28604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28604step0 raw28604; decide +kernel
      have hl : raw28604step0Labels = raw28604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28604 raw28604Labels permutation434 hz
    mixedMoment B raw28604step0 raw28604step0Labels = mixedMoment B raw28604step1 raw28604step1Labels := by
      have hz : ∀ j, raw28604step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28604step1 = (fun i j => raw28604step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28604step1 raw28604step0; decide +kernel
      have hl : raw28604step1Labels = raw28604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28604step0 raw28604step0Labels permutation80 hz
    mixedMoment B raw28604step1 raw28604step1Labels = mixedMoment B raw28604step2 raw28604step2Labels := by
      have ha : raw28604step2 = (fun i j => raw28604step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28604step2 raw28604step1; decide +kernel
      have hl : raw28604step2Labels = raw28604step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28604step1 raw28604step1Labels permutation31 permutation2
    mixedMoment B raw28604step2 raw28604step2Labels = mixedMoment B raw28604step3 raw28604step3Labels := by
      have ha : raw28604step3 = -raw28604step2 := by apply Matrix.ext; change ∀ i j, raw28604step3 i j = -(raw28604step2 i j); unfold raw28604step3 raw28604step2; decide +kernel
      have hl : raw28604step3Labels = raw28604step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw28605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28605 raw28605Labels = mixedMoment B node1978 node1978Labels := by
  calc
    mixedMoment B raw28605 raw28605Labels = mixedMoment B raw28605step0 raw28605step0Labels := by
      have hz : ∀ j, raw28605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28605step0 = (fun i j => raw28605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28605step0 raw28605; decide +kernel
      have hl : raw28605step0Labels = raw28605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28605 raw28605Labels permutation434 hz
    mixedMoment B raw28605step0 raw28605step0Labels = mixedMoment B raw28605step1 raw28605step1Labels := by
      have ha : raw28605step1 = (fun i j => raw28605step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28605step1 raw28605step0; decide +kernel
      have hl : raw28605step1Labels = raw28605step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28605step0 raw28605step0Labels permutation145 permutation2
    mixedMoment B raw28605step1 raw28605step1Labels = mixedMoment B raw28605step2 raw28605step2Labels := by
      have ha : raw28605step2 = -raw28605step1 := by apply Matrix.ext; change ∀ i j, raw28605step2 i j = -(raw28605step1 i j); unfold raw28605step2 raw28605step1; decide +kernel
      have hl : raw28605step2Labels = raw28605step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1978 node1978Labels := by rfl

def raw28606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28606 raw28606Labels = mixedMoment B node1978 node1978Labels := by
  calc
    mixedMoment B raw28606 raw28606Labels = mixedMoment B raw28606step0 raw28606step0Labels := by
      have hz : ∀ j, raw28606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28606step0 = (fun i j => raw28606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28606step0 raw28606; decide +kernel
      have hl : raw28606step0Labels = raw28606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28606 raw28606Labels permutation346 hz
    mixedMoment B raw28606step0 raw28606step0Labels = mixedMoment B raw28606step1 raw28606step1Labels := by
      have ha : raw28606step1 = (fun i j => raw28606step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28606step1 raw28606step0; decide +kernel
      have hl : raw28606step1Labels = raw28606step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28606step0 raw28606step0Labels permutation145 permutation2
    mixedMoment B raw28606step1 raw28606step1Labels = mixedMoment B raw28606step2 raw28606step2Labels := by
      have ha : raw28606step2 = -raw28606step1 := by apply Matrix.ext; change ∀ i j, raw28606step2 i j = -(raw28606step1 i j); unfold raw28606step2 raw28606step1; decide +kernel
      have hl : raw28606step2Labels = raw28606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1978 node1978Labels := by rfl

def raw28607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28607step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28607 raw28607Labels = mixedMoment B node1830 node1830Labels := by
  calc
    mixedMoment B raw28607 raw28607Labels = mixedMoment B raw28607step0 raw28607step0Labels := by
      have hz : ∀ j, raw28607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28607step0 = (fun i j => raw28607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28607step0 raw28607; decide +kernel
      have hl : raw28607step0Labels = raw28607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28607 raw28607Labels permutation434 hz
    mixedMoment B raw28607step0 raw28607step0Labels = mixedMoment B raw28607step1 raw28607step1Labels := by
      have hz : ∀ j, raw28607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28607step1 = (fun i j => raw28607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28607step1 raw28607step0; decide +kernel
      have hl : raw28607step1Labels = raw28607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28607step0 raw28607step0Labels permutation80 hz
    mixedMoment B raw28607step1 raw28607step1Labels = mixedMoment B raw28607step2 raw28607step2Labels := by
      have ha : raw28607step2 = (fun i j => raw28607step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28607step2 raw28607step1; decide +kernel
      have hl : raw28607step2Labels = raw28607step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28607step1 raw28607step1Labels permutation31 permutation2
    mixedMoment B raw28607step2 raw28607step2Labels = mixedMoment B raw28607step3 raw28607step3Labels := by
      have ha : raw28607step3 = -raw28607step2 := by apply Matrix.ext; change ∀ i j, raw28607step3 i j = -(raw28607step2 i j); unfold raw28607step3 raw28607step2; decide +kernel
      have hl : raw28607step3Labels = raw28607step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1830 node1830Labels := by rfl

def raw28608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28608step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28608 raw28608Labels = mixedMoment B node952 node952Labels := by
  calc
    mixedMoment B raw28608 raw28608Labels = mixedMoment B raw28608step0 raw28608step0Labels := by
      have hz : ∀ j, raw28608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28608step0 = (fun i j => raw28608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28608step0 raw28608; decide +kernel
      have hl : raw28608step0Labels = raw28608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28608 raw28608Labels permutation434 hz
    mixedMoment B raw28608step0 raw28608step0Labels = mixedMoment B raw28608step1 raw28608step1Labels := by
      have hz : ∀ j, raw28608step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28608step1 = (fun i j => raw28608step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28608step1 raw28608step0; decide +kernel
      have hl : raw28608step1Labels = raw28608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28608step0 raw28608step0Labels permutation80 hz
    mixedMoment B raw28608step1 raw28608step1Labels = mixedMoment B raw28608step2 raw28608step2Labels := by
      have ha : raw28608step2 = (fun i j => raw28608step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28608step2 raw28608step1; decide +kernel
      have hl : raw28608step2Labels = raw28608step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28608step1 raw28608step1Labels permutation31 permutation2
    mixedMoment B raw28608step2 raw28608step2Labels = mixedMoment B raw28608step3 raw28608step3Labels := by
      have ha : raw28608step3 = -raw28608step2 := by apply Matrix.ext; change ∀ i j, raw28608step3 i j = -(raw28608step2 i j); unfold raw28608step3 raw28608step2; decide +kernel
      have hl : raw28608step3Labels = raw28608step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node952 node952Labels := by rfl

def raw28609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28609 raw28609Labels = mixedMoment B node1972 node1972Labels := by
  calc
    mixedMoment B raw28609 raw28609Labels = mixedMoment B raw28609step0 raw28609step0Labels := by
      have ha : raw28609step0 = (fun i j => raw28609 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28609step0 raw28609; decide +kernel
      have hl : raw28609step0Labels = raw28609Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28609 raw28609Labels permutation644 permutation2
    mixedMoment B raw28609step0 raw28609step0Labels = mixedMoment B raw28609step1 raw28609step1Labels := by
      have ha : raw28609step1 = -raw28609step0 := by apply Matrix.ext; change ∀ i j, raw28609step1 i j = -(raw28609step0 i j); unfold raw28609step1 raw28609step0; decide +kernel
      have hl : raw28609step1Labels = raw28609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1972 node1972Labels := by rfl

def raw28610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw28610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw28610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28610 raw28610Labels = mixedMoment B node2588 node2588Labels := by
  calc
    mixedMoment B raw28610 raw28610Labels = mixedMoment B raw28610step0 raw28610step0Labels := by
      have hz : ∀ j, raw28610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28610step0 = (fun i j => raw28610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28610step0 raw28610; decide +kernel
      have hl : raw28610step0Labels = raw28610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28610 raw28610Labels permutation434 hz
    mixedMoment B raw28610step0 raw28610step0Labels = mixedMoment B raw28610step1 raw28610step1Labels := by
      have ha : raw28610step1 = (fun i j => raw28610step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28610step1 raw28610step0; decide +kernel
      have hl : raw28610step1Labels = raw28610step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28610step0 raw28610step0Labels permutation34 permutation2
    _ = mixedMoment B node2588 node2588Labels := by rfl

def raw28611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28611step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28611 raw28611Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw28611 raw28611Labels = mixedMoment B raw28611step0 raw28611step0Labels := by
      have hz : ∀ j, raw28611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28611step0 = (fun i j => raw28611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28611step0 raw28611; decide +kernel
      have hl : raw28611step0Labels = raw28611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28611 raw28611Labels permutation434 hz
    mixedMoment B raw28611step0 raw28611step0Labels = mixedMoment B raw28611step1 raw28611step1Labels := by
      have ha : raw28611step1 = (fun i j => raw28611step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28611step1 raw28611step0; decide +kernel
      have hl : raw28611step1Labels = raw28611step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28611step0 raw28611step0Labels permutation149 permutation2
    mixedMoment B raw28611step1 raw28611step1Labels = mixedMoment B raw28611step2 raw28611step2Labels := by
      have ha : raw28611step2 = -raw28611step1 := by apply Matrix.ext; change ∀ i j, raw28611step2 i j = -(raw28611step1 i j); unfold raw28611step2 raw28611step1; decide +kernel
      have hl : raw28611step2Labels = raw28611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw28612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28612 raw28612Labels = mixedMoment B node1972 node1972Labels := by
  calc
    mixedMoment B raw28612 raw28612Labels = mixedMoment B raw28612step0 raw28612step0Labels := by
      have ha : raw28612step0 = (fun i j => raw28612 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28612step0 raw28612; decide +kernel
      have hl : raw28612step0Labels = raw28612Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28612 raw28612Labels permutation662 permutation2
    mixedMoment B raw28612step0 raw28612step0Labels = mixedMoment B raw28612step1 raw28612step1Labels := by
      have ha : raw28612step1 = -raw28612step0 := by apply Matrix.ext; change ∀ i j, raw28612step1 i j = -(raw28612step0 i j); unfold raw28612step1 raw28612step0; decide +kernel
      have hl : raw28612step1Labels = raw28612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1972 node1972Labels := by rfl

def raw28613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28613 raw28613Labels = mixedMoment B node1823 node1823Labels := by
  calc
    mixedMoment B raw28613 raw28613Labels = mixedMoment B raw28613step0 raw28613step0Labels := by
      have hz : ∀ j, raw28613 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28613step0 = (fun i j => raw28613 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28613step0 raw28613; decide +kernel
      have hl : raw28613step0Labels = raw28613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28613 raw28613Labels permutation434 hz
    mixedMoment B raw28613step0 raw28613step0Labels = mixedMoment B raw28613step1 raw28613step1Labels := by
      have ha : raw28613step1 = (fun i j => raw28613step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28613step1 raw28613step0; decide +kernel
      have hl : raw28613step1Labels = raw28613step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28613step0 raw28613step0Labels permutation149 permutation2
    mixedMoment B raw28613step1 raw28613step1Labels = mixedMoment B raw28613step2 raw28613step2Labels := by
      have ha : raw28613step2 = -raw28613step1 := by apply Matrix.ext; change ∀ i j, raw28613step2 i j = -(raw28613step1 i j); unfold raw28613step2 raw28613step1; decide +kernel
      have hl : raw28613step2Labels = raw28613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1823 node1823Labels := by rfl

def raw28614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28614 raw28614Labels = mixedMoment B node943 node943Labels := by
  calc
    mixedMoment B raw28614 raw28614Labels = mixedMoment B raw28614step0 raw28614step0Labels := by
      have hz : ∀ j, raw28614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28614step0 = (fun i j => raw28614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28614step0 raw28614; decide +kernel
      have hl : raw28614step0Labels = raw28614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28614 raw28614Labels permutation434 hz
    mixedMoment B raw28614step0 raw28614step0Labels = mixedMoment B raw28614step1 raw28614step1Labels := by
      have ha : raw28614step1 = (fun i j => raw28614step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28614step1 raw28614step0; decide +kernel
      have hl : raw28614step1Labels = raw28614step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28614step0 raw28614step0Labels permutation149 permutation2
    mixedMoment B raw28614step1 raw28614step1Labels = mixedMoment B raw28614step2 raw28614step2Labels := by
      have ha : raw28614step2 = -raw28614step1 := by apply Matrix.ext; change ∀ i j, raw28614step2 i j = -(raw28614step1 i j); unfold raw28614step2 raw28614step1; decide +kernel
      have hl : raw28614step2Labels = raw28614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node943 node943Labels := by rfl

def raw28615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28615step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28615step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28615step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28615step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28615 raw28615Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw28615 raw28615Labels = mixedMoment B raw28615step0 raw28615step0Labels := by
      have hz : ∀ j, raw28615 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28615step0 = (fun i j => raw28615 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28615step0 raw28615; decide +kernel
      have hl : raw28615step0Labels = raw28615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28615 raw28615Labels permutation434 hz
    mixedMoment B raw28615step0 raw28615step0Labels = mixedMoment B raw28615step1 raw28615step1Labels := by
      have hz : ∀ j, raw28615step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28615step1 = (fun i j => raw28615step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28615step1 raw28615step0; decide +kernel
      have hl : raw28615step1Labels = raw28615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28615step0 raw28615step0Labels permutation80 hz
    mixedMoment B raw28615step1 raw28615step1Labels = mixedMoment B raw28615step2 raw28615step2Labels := by
      have ha : raw28615step2 = (fun i j => raw28615step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28615step2 raw28615step1; decide +kernel
      have hl : raw28615step2Labels = raw28615step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28615step1 raw28615step1Labels permutation30 permutation3
    mixedMoment B raw28615step2 raw28615step2Labels = mixedMoment B raw28615step3 raw28615step3Labels := by
      have ha : raw28615step3 = -raw28615step2 := by apply Matrix.ext; change ∀ i j, raw28615step3 i j = -(raw28615step2 i j); unfold raw28615step3 raw28615step2; decide +kernel
      have hl : raw28615step3Labels = raw28615step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28615step3 raw28615step3Labels = mixedMoment B raw28615step4 raw28615step4Labels := by
      have ha : raw28615step4 = raw28615step3 := by apply Matrix.ext; unfold raw28615step4 raw28615step3; decide +kernel
      have hl : raw28615step3Labels = labelEmbedding6 ∘ raw28615step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28615step3 raw28615step3Labels raw28615step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

def raw28616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28616step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28616step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28616step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28616 raw28616Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw28616 raw28616Labels = mixedMoment B raw28616step0 raw28616step0Labels := by
      have hz : ∀ j, raw28616 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28616step0 = (fun i j => raw28616 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28616step0 raw28616; decide +kernel
      have hl : raw28616step0Labels = raw28616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28616 raw28616Labels permutation434 hz
    mixedMoment B raw28616step0 raw28616step0Labels = mixedMoment B raw28616step1 raw28616step1Labels := by
      have ha : raw28616step1 = (fun i j => raw28616step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28616step1 raw28616step0; decide +kernel
      have hl : raw28616step1Labels = raw28616step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28616step0 raw28616step0Labels permutation149 permutation3
    mixedMoment B raw28616step1 raw28616step1Labels = mixedMoment B raw28616step2 raw28616step2Labels := by
      have ha : raw28616step2 = -raw28616step1 := by apply Matrix.ext; change ∀ i j, raw28616step2 i j = -(raw28616step1 i j); unfold raw28616step2 raw28616step1; decide +kernel
      have hl : raw28616step2Labels = raw28616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28616step2 raw28616step2Labels = mixedMoment B raw28616step3 raw28616step3Labels := by
      have ha : raw28616step3 = raw28616step2 := by apply Matrix.ext; unfold raw28616step3 raw28616step2; decide +kernel
      have hl : raw28616step2Labels = labelEmbedding6 ∘ raw28616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28616step2 raw28616step2Labels raw28616step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw28617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28617step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28617step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28617step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28617step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28617 raw28617Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw28617 raw28617Labels = mixedMoment B raw28617step0 raw28617step0Labels := by
      have hz : ∀ j, raw28617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28617step0 = (fun i j => raw28617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28617step0 raw28617; decide +kernel
      have hl : raw28617step0Labels = raw28617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28617 raw28617Labels permutation346 hz
    mixedMoment B raw28617step0 raw28617step0Labels = mixedMoment B raw28617step1 raw28617step1Labels := by
      have ha : raw28617step1 = (fun i j => raw28617step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28617step1 raw28617step0; decide +kernel
      have hl : raw28617step1Labels = raw28617step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28617step0 raw28617step0Labels permutation149 permutation3
    mixedMoment B raw28617step1 raw28617step1Labels = mixedMoment B raw28617step2 raw28617step2Labels := by
      have ha : raw28617step2 = -raw28617step1 := by apply Matrix.ext; change ∀ i j, raw28617step2 i j = -(raw28617step1 i j); unfold raw28617step2 raw28617step1; decide +kernel
      have hl : raw28617step2Labels = raw28617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28617step2 raw28617step2Labels = mixedMoment B raw28617step3 raw28617step3Labels := by
      have ha : raw28617step3 = raw28617step2 := by apply Matrix.ext; unfold raw28617step3 raw28617step2; decide +kernel
      have hl : raw28617step2Labels = labelEmbedding6 ∘ raw28617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28617step2 raw28617step2Labels raw28617step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw28618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw28618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28618step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28618 raw28618Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw28618 raw28618Labels = mixedMoment B raw28618step0 raw28618step0Labels := by
      have hz : ∀ j, raw28618 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28618step0 = (fun i j => raw28618 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28618step0 raw28618; decide +kernel
      have hl : raw28618step0Labels = raw28618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28618 raw28618Labels permutation434 hz
    mixedMoment B raw28618step0 raw28618step0Labels = mixedMoment B raw28618step1 raw28618step1Labels := by
      have hz : ∀ j, raw28618step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28618step1 = (fun i j => raw28618step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28618step1 raw28618step0; decide +kernel
      have hl : raw28618step1Labels = raw28618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28618step0 raw28618step0Labels permutation80 hz
    mixedMoment B raw28618step1 raw28618step1Labels = mixedMoment B raw28618step2 raw28618step2Labels := by
      have ha : raw28618step2 = (fun i j => raw28618step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28618step2 raw28618step1; decide +kernel
      have hl : raw28618step2Labels = raw28618step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28618step1 raw28618step1Labels permutation28 permutation5
    mixedMoment B raw28618step2 raw28618step2Labels = mixedMoment B raw28618step3 raw28618step3Labels := by
      have ha : raw28618step3 = raw28618step2 := by apply Matrix.ext; unfold raw28618step3 raw28618step2; decide +kernel
      have hl : raw28618step2Labels = labelEmbedding8 ∘ raw28618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28618step2 raw28618step2Labels raw28618step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw28619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw28619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28619step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28619step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28619 raw28619Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw28619 raw28619Labels = mixedMoment B raw28619step0 raw28619step0Labels := by
      have hz : ∀ j, raw28619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28619step0 = (fun i j => raw28619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28619step0 raw28619; decide +kernel
      have hl : raw28619step0Labels = raw28619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28619 raw28619Labels permutation434 hz
    mixedMoment B raw28619step0 raw28619step0Labels = mixedMoment B raw28619step1 raw28619step1Labels := by
      have hz : ∀ j, raw28619step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28619step1 = (fun i j => raw28619step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28619step1 raw28619step0; decide +kernel
      have hl : raw28619step1Labels = raw28619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28619step0 raw28619step0Labels permutation80 hz
    mixedMoment B raw28619step1 raw28619step1Labels = mixedMoment B raw28619step2 raw28619step2Labels := by
      have ha : raw28619step2 = (fun i j => raw28619step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28619step2 raw28619step1; decide +kernel
      have hl : raw28619step2Labels = raw28619step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28619step1 raw28619step1Labels permutation8 permutation3
    mixedMoment B raw28619step2 raw28619step2Labels = mixedMoment B raw28619step3 raw28619step3Labels := by
      have ha : raw28619step3 = raw28619step2 := by apply Matrix.ext; unfold raw28619step3 raw28619step2; decide +kernel
      have hl : raw28619step2Labels = labelEmbedding6 ∘ raw28619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28619step2 raw28619step2Labels raw28619step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw28620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28620step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28620 raw28620Labels = mixedMoment B node4338 node4338Labels := by
  calc
    mixedMoment B raw28620 raw28620Labels = mixedMoment B raw28620step0 raw28620step0Labels := by
      have hz : ∀ j, raw28620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28620step0 = (fun i j => raw28620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28620step0 raw28620; decide +kernel
      have hl : raw28620step0Labels = raw28620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28620 raw28620Labels permutation434 hz
    mixedMoment B raw28620step0 raw28620step0Labels = mixedMoment B raw28620step1 raw28620step1Labels := by
      have ha : raw28620step1 = (fun i j => raw28620step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28620step1 raw28620step0; decide +kernel
      have hl : raw28620step1Labels = raw28620step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28620step0 raw28620step0Labels permutation34 permutation3
    mixedMoment B raw28620step1 raw28620step1Labels = mixedMoment B raw28620step2 raw28620step2Labels := by
      have ha : raw28620step2 = raw28620step1 := by apply Matrix.ext; unfold raw28620step2 raw28620step1; decide +kernel
      have hl : raw28620step1Labels = labelEmbedding6 ∘ raw28620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28620step1 raw28620step1Labels raw28620step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4338 node4338Labels := by rfl

def raw28621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28621 raw28621Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw28621 raw28621Labels = mixedMoment B raw28621step0 raw28621step0Labels := by
      have hz : ∀ j, raw28621 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28621step0 = (fun i j => raw28621 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28621step0 raw28621; decide +kernel
      have hl : raw28621step0Labels = raw28621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28621 raw28621Labels permutation434 hz
    mixedMoment B raw28621step0 raw28621step0Labels = mixedMoment B raw28621step1 raw28621step1Labels := by
      have ha : raw28621step1 = (fun i j => raw28621step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28621step1 raw28621step0; decide +kernel
      have hl : raw28621step1Labels = raw28621step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28621step0 raw28621step0Labels permutation145 permutation3
    mixedMoment B raw28621step1 raw28621step1Labels = mixedMoment B raw28621step2 raw28621step2Labels := by
      have ha : raw28621step2 = -raw28621step1 := by apply Matrix.ext; change ∀ i j, raw28621step2 i j = -(raw28621step1 i j); unfold raw28621step2 raw28621step1; decide +kernel
      have hl : raw28621step2Labels = raw28621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28621step2 raw28621step2Labels = mixedMoment B raw28621step3 raw28621step3Labels := by
      have ha : raw28621step3 = raw28621step2 := by apply Matrix.ext; unfold raw28621step3 raw28621step2; decide +kernel
      have hl : raw28621step2Labels = labelEmbedding6 ∘ raw28621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28621step2 raw28621step2Labels raw28621step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

def raw28622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28622step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28622step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28622step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28622step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28622 raw28622Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw28622 raw28622Labels = mixedMoment B raw28622step0 raw28622step0Labels := by
      have ha : raw28622step0 = (fun i j => raw28622 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28622step0 raw28622; decide +kernel
      have hl : raw28622step0Labels = raw28622Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28622 raw28622Labels permutation644 permutation3
    mixedMoment B raw28622step0 raw28622step0Labels = mixedMoment B raw28622step1 raw28622step1Labels := by
      have ha : raw28622step1 = -raw28622step0 := by apply Matrix.ext; change ∀ i j, raw28622step1 i j = -(raw28622step0 i j); unfold raw28622step1 raw28622step0; decide +kernel
      have hl : raw28622step1Labels = raw28622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28622step1 raw28622step1Labels = mixedMoment B raw28622step2 raw28622step2Labels := by
      have ha : raw28622step2 = raw28622step1 := by apply Matrix.ext; unfold raw28622step2 raw28622step1; decide +kernel
      have hl : raw28622step1Labels = labelEmbedding6 ∘ raw28622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28622step1 raw28622step1Labels raw28622step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4721 node4721Labels := by rfl

def raw28623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28623step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28623 raw28623Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw28623 raw28623Labels = mixedMoment B raw28623step0 raw28623step0Labels := by
      have hz : ∀ j, raw28623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28623step0 = (fun i j => raw28623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28623step0 raw28623; decide +kernel
      have hl : raw28623step0Labels = raw28623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28623 raw28623Labels permutation434 hz
    mixedMoment B raw28623step0 raw28623step0Labels = mixedMoment B raw28623step1 raw28623step1Labels := by
      have ha : raw28623step1 = (fun i j => raw28623step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28623step1 raw28623step0; decide +kernel
      have hl : raw28623step1Labels = raw28623step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28623step0 raw28623step0Labels permutation143 permutation5
    mixedMoment B raw28623step1 raw28623step1Labels = mixedMoment B raw28623step2 raw28623step2Labels := by
      have ha : raw28623step2 = raw28623step1 := by apply Matrix.ext; unfold raw28623step2 raw28623step1; decide +kernel
      have hl : raw28623step1Labels = labelEmbedding8 ∘ raw28623step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28623step1 raw28623step1Labels raw28623step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw28624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28624step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28624 raw28624Labels = mixedMoment B node4338 node4338Labels := by
  calc
    mixedMoment B raw28624 raw28624Labels = mixedMoment B raw28624step0 raw28624step0Labels := by
      have hz : ∀ j, raw28624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28624step0 = (fun i j => raw28624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28624step0 raw28624; decide +kernel
      have hl : raw28624step0Labels = raw28624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28624 raw28624Labels permutation346 hz
    mixedMoment B raw28624step0 raw28624step0Labels = mixedMoment B raw28624step1 raw28624step1Labels := by
      have ha : raw28624step1 = (fun i j => raw28624step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28624step1 raw28624step0; decide +kernel
      have hl : raw28624step1Labels = raw28624step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28624step0 raw28624step0Labels permutation34 permutation3
    mixedMoment B raw28624step1 raw28624step1Labels = mixedMoment B raw28624step2 raw28624step2Labels := by
      have ha : raw28624step2 = raw28624step1 := by apply Matrix.ext; unfold raw28624step2 raw28624step1; decide +kernel
      have hl : raw28624step1Labels = labelEmbedding6 ∘ raw28624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28624step1 raw28624step1Labels raw28624step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4338 node4338Labels := by rfl

def raw28625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28625step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28625step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28625step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28625step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28625 raw28625Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw28625 raw28625Labels = mixedMoment B raw28625step0 raw28625step0Labels := by
      have hz : ∀ j, raw28625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28625step0 = (fun i j => raw28625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28625step0 raw28625; decide +kernel
      have hl : raw28625step0Labels = raw28625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28625 raw28625Labels permutation346 hz
    mixedMoment B raw28625step0 raw28625step0Labels = mixedMoment B raw28625step1 raw28625step1Labels := by
      have ha : raw28625step1 = (fun i j => raw28625step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28625step1 raw28625step0; decide +kernel
      have hl : raw28625step1Labels = raw28625step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28625step0 raw28625step0Labels permutation145 permutation3
    mixedMoment B raw28625step1 raw28625step1Labels = mixedMoment B raw28625step2 raw28625step2Labels := by
      have ha : raw28625step2 = -raw28625step1 := by apply Matrix.ext; change ∀ i j, raw28625step2 i j = -(raw28625step1 i j); unfold raw28625step2 raw28625step1; decide +kernel
      have hl : raw28625step2Labels = raw28625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28625step2 raw28625step2Labels = mixedMoment B raw28625step3 raw28625step3Labels := by
      have ha : raw28625step3 = raw28625step2 := by apply Matrix.ext; unfold raw28625step3 raw28625step2; decide +kernel
      have hl : raw28625step2Labels = labelEmbedding6 ∘ raw28625step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28625step2 raw28625step2Labels raw28625step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

def raw28626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28626step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28626step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28626step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28626 raw28626Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw28626 raw28626Labels = mixedMoment B raw28626step0 raw28626step0Labels := by
      have ha : raw28626step0 = (fun i j => raw28626 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28626step0 raw28626; decide +kernel
      have hl : raw28626step0Labels = raw28626Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28626 raw28626Labels permutation662 permutation3
    mixedMoment B raw28626step0 raw28626step0Labels = mixedMoment B raw28626step1 raw28626step1Labels := by
      have ha : raw28626step1 = -raw28626step0 := by apply Matrix.ext; change ∀ i j, raw28626step1 i j = -(raw28626step0 i j); unfold raw28626step1 raw28626step0; decide +kernel
      have hl : raw28626step1Labels = raw28626step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28626step1 raw28626step1Labels = mixedMoment B raw28626step2 raw28626step2Labels := by
      have ha : raw28626step2 = raw28626step1 := by apply Matrix.ext; unfold raw28626step2 raw28626step1; decide +kernel
      have hl : raw28626step1Labels = labelEmbedding6 ∘ raw28626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28626step1 raw28626step1Labels raw28626step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4721 node4721Labels := by rfl

def raw28627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28627step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28627 raw28627Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw28627 raw28627Labels = mixedMoment B raw28627step0 raw28627step0Labels := by
      have hz : ∀ j, raw28627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28627step0 = (fun i j => raw28627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28627step0 raw28627; decide +kernel
      have hl : raw28627step0Labels = raw28627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28627 raw28627Labels permutation346 hz
    mixedMoment B raw28627step0 raw28627step0Labels = mixedMoment B raw28627step1 raw28627step1Labels := by
      have ha : raw28627step1 = (fun i j => raw28627step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28627step1 raw28627step0; decide +kernel
      have hl : raw28627step1Labels = raw28627step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28627step0 raw28627step0Labels permutation143 permutation5
    mixedMoment B raw28627step1 raw28627step1Labels = mixedMoment B raw28627step2 raw28627step2Labels := by
      have ha : raw28627step2 = raw28627step1 := by apply Matrix.ext; unfold raw28627step2 raw28627step1; decide +kernel
      have hl : raw28627step1Labels = labelEmbedding8 ∘ raw28627step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28627step1 raw28627step1Labels raw28627step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw28628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28628step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28628step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28628 raw28628Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw28628 raw28628Labels = mixedMoment B raw28628step0 raw28628step0Labels := by
      have hz : ∀ j, raw28628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28628step0 = (fun i j => raw28628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28628step0 raw28628; decide +kernel
      have hl : raw28628step0Labels = raw28628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28628 raw28628Labels permutation434 hz
    mixedMoment B raw28628step0 raw28628step0Labels = mixedMoment B raw28628step1 raw28628step1Labels := by
      have hz : ∀ j, raw28628step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28628step1 = (fun i j => raw28628step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28628step1 raw28628step0; decide +kernel
      have hl : raw28628step1Labels = raw28628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28628step0 raw28628step0Labels permutation80 hz
    mixedMoment B raw28628step1 raw28628step1Labels = mixedMoment B raw28628step2 raw28628step2Labels := by
      have ha : raw28628step2 = (fun i j => raw28628step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28628step2 raw28628step1; decide +kernel
      have hl : raw28628step2Labels = raw28628step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28628step1 raw28628step1Labels permutation8 permutation3
    mixedMoment B raw28628step2 raw28628step2Labels = mixedMoment B raw28628step3 raw28628step3Labels := by
      have ha : raw28628step3 = raw28628step2 := by apply Matrix.ext; unfold raw28628step3 raw28628step2; decide +kernel
      have hl : raw28628step2Labels = labelEmbedding6 ∘ raw28628step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28628step2 raw28628step2Labels raw28628step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4359 node4359Labels := by rfl

def raw28629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28629step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28629step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28629step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28629step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28629step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28629 raw28629Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw28629 raw28629Labels = mixedMoment B raw28629step0 raw28629step0Labels := by
      have hz : ∀ j, raw28629 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28629step0 = (fun i j => raw28629 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28629step0 raw28629; decide +kernel
      have hl : raw28629step0Labels = raw28629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28629 raw28629Labels permutation434 hz
    mixedMoment B raw28629step0 raw28629step0Labels = mixedMoment B raw28629step1 raw28629step1Labels := by
      have hz : ∀ j, raw28629step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28629step1 = (fun i j => raw28629step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28629step1 raw28629step0; decide +kernel
      have hl : raw28629step1Labels = raw28629step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28629step0 raw28629step0Labels permutation80 hz
    mixedMoment B raw28629step1 raw28629step1Labels = mixedMoment B raw28629step2 raw28629step2Labels := by
      have ha : raw28629step2 = (fun i j => raw28629step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28629step2 raw28629step1; decide +kernel
      have hl : raw28629step2Labels = raw28629step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28629step1 raw28629step1Labels permutation31 permutation3
    mixedMoment B raw28629step2 raw28629step2Labels = mixedMoment B raw28629step3 raw28629step3Labels := by
      have ha : raw28629step3 = -raw28629step2 := by apply Matrix.ext; change ∀ i j, raw28629step3 i j = -(raw28629step2 i j); unfold raw28629step3 raw28629step2; decide +kernel
      have hl : raw28629step3Labels = raw28629step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28629step3 raw28629step3Labels = mixedMoment B raw28629step4 raw28629step4Labels := by
      have ha : raw28629step4 = raw28629step3 := by apply Matrix.ext; unfold raw28629step4 raw28629step3; decide +kernel
      have hl : raw28629step3Labels = labelEmbedding6 ∘ raw28629step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28629step3 raw28629step3Labels raw28629step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4692 node4692Labels := by rfl

def raw28630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28630step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28630step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28630step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28630 raw28630Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw28630 raw28630Labels = mixedMoment B raw28630step0 raw28630step0Labels := by
      have hz : ∀ j, raw28630 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28630step0 = (fun i j => raw28630 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28630step0 raw28630; decide +kernel
      have hl : raw28630step0Labels = raw28630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28630 raw28630Labels permutation434 hz
    mixedMoment B raw28630step0 raw28630step0Labels = mixedMoment B raw28630step1 raw28630step1Labels := by
      have ha : raw28630step1 = (fun i j => raw28630step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28630step1 raw28630step0; decide +kernel
      have hl : raw28630step1Labels = raw28630step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28630step0 raw28630step0Labels permutation149 permutation3
    mixedMoment B raw28630step1 raw28630step1Labels = mixedMoment B raw28630step2 raw28630step2Labels := by
      have ha : raw28630step2 = -raw28630step1 := by apply Matrix.ext; change ∀ i j, raw28630step2 i j = -(raw28630step1 i j); unfold raw28630step2 raw28630step1; decide +kernel
      have hl : raw28630step2Labels = raw28630step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28630step2 raw28630step2Labels = mixedMoment B raw28630step3 raw28630step3Labels := by
      have ha : raw28630step3 = raw28630step2 := by apply Matrix.ext; unfold raw28630step3 raw28630step2; decide +kernel
      have hl : raw28630step2Labels = labelEmbedding6 ∘ raw28630step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28630step2 raw28630step2Labels raw28630step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw28631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28631step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28631step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28631step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28631step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28631 raw28631Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw28631 raw28631Labels = mixedMoment B raw28631step0 raw28631step0Labels := by
      have hz : ∀ j, raw28631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28631step0 = (fun i j => raw28631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28631step0 raw28631; decide +kernel
      have hl : raw28631step0Labels = raw28631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28631 raw28631Labels permutation346 hz
    mixedMoment B raw28631step0 raw28631step0Labels = mixedMoment B raw28631step1 raw28631step1Labels := by
      have ha : raw28631step1 = (fun i j => raw28631step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28631step1 raw28631step0; decide +kernel
      have hl : raw28631step1Labels = raw28631step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28631step0 raw28631step0Labels permutation149 permutation3
    mixedMoment B raw28631step1 raw28631step1Labels = mixedMoment B raw28631step2 raw28631step2Labels := by
      have ha : raw28631step2 = -raw28631step1 := by apply Matrix.ext; change ∀ i j, raw28631step2 i j = -(raw28631step1 i j); unfold raw28631step2 raw28631step1; decide +kernel
      have hl : raw28631step2Labels = raw28631step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28631step2 raw28631step2Labels = mixedMoment B raw28631step3 raw28631step3Labels := by
      have ha : raw28631step3 = raw28631step2 := by apply Matrix.ext; unfold raw28631step3 raw28631step2; decide +kernel
      have hl : raw28631step2Labels = labelEmbedding6 ∘ raw28631step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28631step2 raw28631step2Labels raw28631step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw28632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28632step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28632step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28632step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28632step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28632 raw28632Labels = mixedMoment B node4235 node4235Labels := by
  calc
    mixedMoment B raw28632 raw28632Labels = mixedMoment B raw28632step0 raw28632step0Labels := by
      have hz : ∀ j, raw28632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28632step0 = (fun i j => raw28632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28632step0 raw28632; decide +kernel
      have hl : raw28632step0Labels = raw28632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28632 raw28632Labels permutation434 hz
    mixedMoment B raw28632step0 raw28632step0Labels = mixedMoment B raw28632step1 raw28632step1Labels := by
      have hz : ∀ j, raw28632step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28632step1 = (fun i j => raw28632step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28632step1 raw28632step0; decide +kernel
      have hl : raw28632step1Labels = raw28632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28632step0 raw28632step0Labels permutation80 hz
    mixedMoment B raw28632step1 raw28632step1Labels = mixedMoment B raw28632step2 raw28632step2Labels := by
      have ha : raw28632step2 = (fun i j => raw28632step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28632step2 raw28632step1; decide +kernel
      have hl : raw28632step2Labels = raw28632step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28632step1 raw28632step1Labels permutation31 permutation3
    mixedMoment B raw28632step2 raw28632step2Labels = mixedMoment B raw28632step3 raw28632step3Labels := by
      have ha : raw28632step3 = -raw28632step2 := by apply Matrix.ext; change ∀ i j, raw28632step3 i j = -(raw28632step2 i j); unfold raw28632step3 raw28632step2; decide +kernel
      have hl : raw28632step3Labels = raw28632step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28632step3 raw28632step3Labels = mixedMoment B raw28632step4 raw28632step4Labels := by
      have ha : raw28632step4 = raw28632step3 := by apply Matrix.ext; unfold raw28632step4 raw28632step3; decide +kernel
      have hl : raw28632step3Labels = labelEmbedding6 ∘ raw28632step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28632step3 raw28632step3Labels raw28632step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4235 node4235Labels := by rfl

def raw28633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28633step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28633step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28633step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28633step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28633step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28633 raw28633Labels = mixedMoment B node4242 node4242Labels := by
  calc
    mixedMoment B raw28633 raw28633Labels = mixedMoment B raw28633step0 raw28633step0Labels := by
      have hz : ∀ j, raw28633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28633step0 = (fun i j => raw28633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28633step0 raw28633; decide +kernel
      have hl : raw28633step0Labels = raw28633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28633 raw28633Labels permutation434 hz
    mixedMoment B raw28633step0 raw28633step0Labels = mixedMoment B raw28633step1 raw28633step1Labels := by
      have hz : ∀ j, raw28633step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28633step1 = (fun i j => raw28633step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28633step1 raw28633step0; decide +kernel
      have hl : raw28633step1Labels = raw28633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28633step0 raw28633step0Labels permutation80 hz
    mixedMoment B raw28633step1 raw28633step1Labels = mixedMoment B raw28633step2 raw28633step2Labels := by
      have ha : raw28633step2 = (fun i j => raw28633step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28633step2 raw28633step1; decide +kernel
      have hl : raw28633step2Labels = raw28633step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28633step1 raw28633step1Labels permutation31 permutation3
    mixedMoment B raw28633step2 raw28633step2Labels = mixedMoment B raw28633step3 raw28633step3Labels := by
      have ha : raw28633step3 = -raw28633step2 := by apply Matrix.ext; change ∀ i j, raw28633step3 i j = -(raw28633step2 i j); unfold raw28633step3 raw28633step2; decide +kernel
      have hl : raw28633step3Labels = raw28633step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28633step3 raw28633step3Labels = mixedMoment B raw28633step4 raw28633step4Labels := by
      have ha : raw28633step4 = raw28633step3 := by apply Matrix.ext; unfold raw28633step4 raw28633step3; decide +kernel
      have hl : raw28633step3Labels = labelEmbedding6 ∘ raw28633step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28633step3 raw28633step3Labels raw28633step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4242 node4242Labels := by rfl

def raw28634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28634step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28634step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28634 raw28634Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw28634 raw28634Labels = mixedMoment B raw28634step0 raw28634step0Labels := by
      have hz : ∀ j, raw28634 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28634step0 = (fun i j => raw28634 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28634step0 raw28634; decide +kernel
      have hl : raw28634step0Labels = raw28634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28634 raw28634Labels permutation434 hz
    mixedMoment B raw28634step0 raw28634step0Labels = mixedMoment B raw28634step1 raw28634step1Labels := by
      have ha : raw28634step1 = (fun i j => raw28634step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28634step1 raw28634step0; decide +kernel
      have hl : raw28634step1Labels = raw28634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28634step0 raw28634step0Labels permutation149 permutation3
    mixedMoment B raw28634step1 raw28634step1Labels = mixedMoment B raw28634step2 raw28634step2Labels := by
      have ha : raw28634step2 = -raw28634step1 := by apply Matrix.ext; change ∀ i j, raw28634step2 i j = -(raw28634step1 i j); unfold raw28634step2 raw28634step1; decide +kernel
      have hl : raw28634step2Labels = raw28634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28634step2 raw28634step2Labels = mixedMoment B raw28634step3 raw28634step3Labels := by
      have ha : raw28634step3 = raw28634step2 := by apply Matrix.ext; unfold raw28634step3 raw28634step2; decide +kernel
      have hl : raw28634step2Labels = labelEmbedding6 ∘ raw28634step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28634step2 raw28634step2Labels raw28634step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4233 node4233Labels := by rfl

def raw28635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28635step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28635step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28635step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28635 raw28635Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw28635 raw28635Labels = mixedMoment B raw28635step0 raw28635step0Labels := by
      have hz : ∀ j, raw28635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28635step0 = (fun i j => raw28635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28635step0 raw28635; decide +kernel
      have hl : raw28635step0Labels = raw28635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28635 raw28635Labels permutation346 hz
    mixedMoment B raw28635step0 raw28635step0Labels = mixedMoment B raw28635step1 raw28635step1Labels := by
      have ha : raw28635step1 = (fun i j => raw28635step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28635step1 raw28635step0; decide +kernel
      have hl : raw28635step1Labels = raw28635step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28635step0 raw28635step0Labels permutation149 permutation3
    mixedMoment B raw28635step1 raw28635step1Labels = mixedMoment B raw28635step2 raw28635step2Labels := by
      have ha : raw28635step2 = -raw28635step1 := by apply Matrix.ext; change ∀ i j, raw28635step2 i j = -(raw28635step1 i j); unfold raw28635step2 raw28635step1; decide +kernel
      have hl : raw28635step2Labels = raw28635step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28635step2 raw28635step2Labels = mixedMoment B raw28635step3 raw28635step3Labels := by
      have ha : raw28635step3 = raw28635step2 := by apply Matrix.ext; unfold raw28635step3 raw28635step2; decide +kernel
      have hl : raw28635step2Labels = labelEmbedding6 ∘ raw28635step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28635step2 raw28635step2Labels raw28635step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4233 node4233Labels := by rfl

def raw28636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![4, -4, 0]]
def raw28636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28636step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28636step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28636 raw28636Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw28636 raw28636Labels = mixedMoment B raw28636step0 raw28636step0Labels := by
      have hz : ∀ j, raw28636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28636step0 = (fun i j => raw28636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28636step0 raw28636; decide +kernel
      have hl : raw28636step0Labels = raw28636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28636 raw28636Labels permutation434 hz
    mixedMoment B raw28636step0 raw28636step0Labels = mixedMoment B raw28636step1 raw28636step1Labels := by
      have hz : ∀ j, raw28636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28636step1 = (fun i j => raw28636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28636step1 raw28636step0; decide +kernel
      have hl : raw28636step1Labels = raw28636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28636step0 raw28636step0Labels permutation80 hz
    mixedMoment B raw28636step1 raw28636step1Labels = mixedMoment B raw28636step2 raw28636step2Labels := by
      have ha : raw28636step2 = (fun i j => raw28636step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28636step2 raw28636step1; decide +kernel
      have hl : raw28636step2Labels = raw28636step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28636step1 raw28636step1Labels permutation29 permutation5
    mixedMoment B raw28636step2 raw28636step2Labels = mixedMoment B raw28636step3 raw28636step3Labels := by
      have ha : raw28636step3 = raw28636step2 := by apply Matrix.ext; unfold raw28636step3 raw28636step2; decide +kernel
      have hl : raw28636step2Labels = labelEmbedding8 ∘ raw28636step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28636step2 raw28636step2Labels raw28636step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw28637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28637step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28637 raw28637Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw28637 raw28637Labels = mixedMoment B raw28637step0 raw28637step0Labels := by
      have hz : ∀ j, raw28637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28637step0 = (fun i j => raw28637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28637step0 raw28637; decide +kernel
      have hl : raw28637step0Labels = raw28637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28637 raw28637Labels permutation434 hz
    mixedMoment B raw28637step0 raw28637step0Labels = mixedMoment B raw28637step1 raw28637step1Labels := by
      have hz : ∀ j, raw28637step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28637step1 = (fun i j => raw28637step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28637step1 raw28637step0; decide +kernel
      have hl : raw28637step1Labels = raw28637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28637step0 raw28637step0Labels permutation80 hz
    mixedMoment B raw28637step1 raw28637step1Labels = mixedMoment B raw28637step2 raw28637step2Labels := by
      have ha : raw28637step2 = (fun i j => raw28637step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28637step2 raw28637step1; decide +kernel
      have hl : raw28637step2Labels = raw28637step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28637step1 raw28637step1Labels permutation30 permutation3
    mixedMoment B raw28637step2 raw28637step2Labels = mixedMoment B raw28637step3 raw28637step3Labels := by
      have ha : raw28637step3 = -raw28637step2 := by apply Matrix.ext; change ∀ i j, raw28637step3 i j = -(raw28637step2 i j); unfold raw28637step3 raw28637step2; decide +kernel
      have hl : raw28637step3Labels = raw28637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2116 node2116Labels := by rfl

def raw28638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28638 raw28638Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw28638 raw28638Labels = mixedMoment B raw28638step0 raw28638step0Labels := by
      have hz : ∀ j, raw28638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28638step0 = (fun i j => raw28638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28638step0 raw28638; decide +kernel
      have hl : raw28638step0Labels = raw28638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28638 raw28638Labels permutation434 hz
    mixedMoment B raw28638step0 raw28638step0Labels = mixedMoment B raw28638step1 raw28638step1Labels := by
      have ha : raw28638step1 = (fun i j => raw28638step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28638step1 raw28638step0; decide +kernel
      have hl : raw28638step1Labels = raw28638step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28638step0 raw28638step0Labels permutation149 permutation3
    mixedMoment B raw28638step1 raw28638step1Labels = mixedMoment B raw28638step2 raw28638step2Labels := by
      have ha : raw28638step2 = -raw28638step1 := by apply Matrix.ext; change ∀ i j, raw28638step2 i j = -(raw28638step1 i j); unfold raw28638step2 raw28638step1; decide +kernel
      have hl : raw28638step2Labels = raw28638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw28639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28639 raw28639Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw28639 raw28639Labels = mixedMoment B raw28639step0 raw28639step0Labels := by
      have hz : ∀ j, raw28639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28639step0 = (fun i j => raw28639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28639step0 raw28639; decide +kernel
      have hl : raw28639step0Labels = raw28639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28639 raw28639Labels permutation346 hz
    mixedMoment B raw28639step0 raw28639step0Labels = mixedMoment B raw28639step1 raw28639step1Labels := by
      have ha : raw28639step1 = (fun i j => raw28639step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28639step1 raw28639step0; decide +kernel
      have hl : raw28639step1Labels = raw28639step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28639step0 raw28639step0Labels permutation149 permutation3
    mixedMoment B raw28639step1 raw28639step1Labels = mixedMoment B raw28639step2 raw28639step2Labels := by
      have ha : raw28639step2 = -raw28639step1 := by apply Matrix.ext; change ∀ i j, raw28639step2 i j = -(raw28639step1 i j); unfold raw28639step2 raw28639step1; decide +kernel
      have hl : raw28639step2Labels = raw28639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw28640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw28640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw28640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw28640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28640 raw28640Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw28640 raw28640Labels = mixedMoment B raw28640step0 raw28640step0Labels := by
      have hz : ∀ j, raw28640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28640step0 = (fun i j => raw28640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28640step0 raw28640; decide +kernel
      have hl : raw28640step0Labels = raw28640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28640 raw28640Labels permutation434 hz
    mixedMoment B raw28640step0 raw28640step0Labels = mixedMoment B raw28640step1 raw28640step1Labels := by
      have hz : ∀ j, raw28640step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28640step1 = (fun i j => raw28640step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28640step1 raw28640step0; decide +kernel
      have hl : raw28640step1Labels = raw28640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28640step0 raw28640step0Labels permutation80 hz
    mixedMoment B raw28640step1 raw28640step1Labels = mixedMoment B raw28640step2 raw28640step2Labels := by
      have ha : raw28640step2 = (fun i j => raw28640step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28640step2 raw28640step1; decide +kernel
      have hl : raw28640step2Labels = raw28640step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28640step1 raw28640step1Labels permutation31 permutation3
    mixedMoment B raw28640step2 raw28640step2Labels = mixedMoment B raw28640step3 raw28640step3Labels := by
      have ha : raw28640step3 = -raw28640step2 := by apply Matrix.ext; change ∀ i j, raw28640step3 i j = -(raw28640step2 i j); unfold raw28640step3 raw28640step2; decide +kernel
      have hl : raw28640step3Labels = raw28640step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw28641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw28641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28641 raw28641Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw28641 raw28641Labels = mixedMoment B raw28641step0 raw28641step0Labels := by
      have hz : ∀ j, raw28641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28641step0 = (fun i j => raw28641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28641step0 raw28641; decide +kernel
      have hl : raw28641step0Labels = raw28641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28641 raw28641Labels permutation434 hz
    mixedMoment B raw28641step0 raw28641step0Labels = mixedMoment B raw28641step1 raw28641step1Labels := by
      have hz : ∀ j, raw28641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28641step1 = (fun i j => raw28641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28641step1 raw28641step0; decide +kernel
      have hl : raw28641step1Labels = raw28641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28641step0 raw28641step0Labels permutation80 hz
    mixedMoment B raw28641step1 raw28641step1Labels = mixedMoment B raw28641step2 raw28641step2Labels := by
      have ha : raw28641step2 = (fun i j => raw28641step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28641step2 raw28641step1; decide +kernel
      have hl : raw28641step2Labels = raw28641step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28641step1 raw28641step1Labels permutation8 permutation3
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw28642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28642 raw28642Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw28642 raw28642Labels = mixedMoment B raw28642step0 raw28642step0Labels := by
      have hz : ∀ j, raw28642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28642step0 = (fun i j => raw28642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28642step0 raw28642; decide +kernel
      have hl : raw28642step0Labels = raw28642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28642 raw28642Labels permutation434 hz
    mixedMoment B raw28642step0 raw28642step0Labels = mixedMoment B raw28642step1 raw28642step1Labels := by
      have ha : raw28642step1 = (fun i j => raw28642step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28642step1 raw28642step0; decide +kernel
      have hl : raw28642step1Labels = raw28642step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28642step0 raw28642step0Labels permutation34 permutation3
    _ = mixedMoment B node916 node916Labels := by rfl

def raw28643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28643 raw28643Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw28643 raw28643Labels = mixedMoment B raw28643step0 raw28643step0Labels := by
      have hz : ∀ j, raw28643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28643step0 = (fun i j => raw28643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28643step0 raw28643; decide +kernel
      have hl : raw28643step0Labels = raw28643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28643 raw28643Labels permutation434 hz
    mixedMoment B raw28643step0 raw28643step0Labels = mixedMoment B raw28643step1 raw28643step1Labels := by
      have ha : raw28643step1 = (fun i j => raw28643step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28643step1 raw28643step0; decide +kernel
      have hl : raw28643step1Labels = raw28643step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28643step0 raw28643step0Labels permutation145 permutation3
    mixedMoment B raw28643step1 raw28643step1Labels = mixedMoment B raw28643step2 raw28643step2Labels := by
      have ha : raw28643step2 = -raw28643step1 := by apply Matrix.ext; change ∀ i j, raw28643step2 i j = -(raw28643step1 i j); unfold raw28643step2 raw28643step1; decide +kernel
      have hl : raw28643step2Labels = raw28643step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw28644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28644 raw28644Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw28644 raw28644Labels = mixedMoment B raw28644step0 raw28644step0Labels := by
      have ha : raw28644step0 = (fun i j => raw28644 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28644step0 raw28644; decide +kernel
      have hl : raw28644step0Labels = raw28644Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28644 raw28644Labels permutation644 permutation3
    mixedMoment B raw28644step0 raw28644step0Labels = mixedMoment B raw28644step1 raw28644step1Labels := by
      have ha : raw28644step1 = -raw28644step0 := by apply Matrix.ext; change ∀ i j, raw28644step1 i j = -(raw28644step0 i j); unfold raw28644step1 raw28644step0; decide +kernel
      have hl : raw28644step1Labels = raw28644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1875 node1875Labels := by rfl

def raw28645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28645 raw28645Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw28645 raw28645Labels = mixedMoment B raw28645step0 raw28645step0Labels := by
      have hz : ∀ j, raw28645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28645step0 = (fun i j => raw28645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28645step0 raw28645; decide +kernel
      have hl : raw28645step0Labels = raw28645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28645 raw28645Labels permutation434 hz
    mixedMoment B raw28645step0 raw28645step0Labels = mixedMoment B raw28645step1 raw28645step1Labels := by
      have ha : raw28645step1 = (fun i j => raw28645step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28645step1 raw28645step0; decide +kernel
      have hl : raw28645step1Labels = raw28645step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28645step0 raw28645step0Labels permutation145 permutation3
    mixedMoment B raw28645step1 raw28645step1Labels = mixedMoment B raw28645step2 raw28645step2Labels := by
      have ha : raw28645step2 = -raw28645step1 := by apply Matrix.ext; change ∀ i j, raw28645step2 i j = -(raw28645step1 i j); unfold raw28645step2 raw28645step1; decide +kernel
      have hl : raw28645step2Labels = raw28645step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1924 node1924Labels := by rfl

def raw28646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28646 raw28646Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw28646 raw28646Labels = mixedMoment B raw28646step0 raw28646step0Labels := by
      have hz : ∀ j, raw28646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28646step0 = (fun i j => raw28646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28646step0 raw28646; decide +kernel
      have hl : raw28646step0Labels = raw28646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28646 raw28646Labels permutation346 hz
    mixedMoment B raw28646step0 raw28646step0Labels = mixedMoment B raw28646step1 raw28646step1Labels := by
      have ha : raw28646step1 = (fun i j => raw28646step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28646step1 raw28646step0; decide +kernel
      have hl : raw28646step1Labels = raw28646step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28646step0 raw28646step0Labels permutation34 permutation3
    _ = mixedMoment B node916 node916Labels := by rfl

def raw28647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28647 raw28647Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw28647 raw28647Labels = mixedMoment B raw28647step0 raw28647step0Labels := by
      have hz : ∀ j, raw28647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28647step0 = (fun i j => raw28647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28647step0 raw28647; decide +kernel
      have hl : raw28647step0Labels = raw28647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28647 raw28647Labels permutation346 hz
    mixedMoment B raw28647step0 raw28647step0Labels = mixedMoment B raw28647step1 raw28647step1Labels := by
      have ha : raw28647step1 = (fun i j => raw28647step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28647step1 raw28647step0; decide +kernel
      have hl : raw28647step1Labels = raw28647step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28647step0 raw28647step0Labels permutation145 permutation3
    mixedMoment B raw28647step1 raw28647step1Labels = mixedMoment B raw28647step2 raw28647step2Labels := by
      have ha : raw28647step2 = -raw28647step1 := by apply Matrix.ext; change ∀ i j, raw28647step2 i j = -(raw28647step1 i j); unfold raw28647step2 raw28647step1; decide +kernel
      have hl : raw28647step2Labels = raw28647step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw28648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28648 raw28648Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw28648 raw28648Labels = mixedMoment B raw28648step0 raw28648step0Labels := by
      have ha : raw28648step0 = (fun i j => raw28648 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28648step0 raw28648; decide +kernel
      have hl : raw28648step0Labels = raw28648Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28648 raw28648Labels permutation662 permutation3
    mixedMoment B raw28648step0 raw28648step0Labels = mixedMoment B raw28648step1 raw28648step1Labels := by
      have ha : raw28648step1 = -raw28648step0 := by apply Matrix.ext; change ∀ i j, raw28648step1 i j = -(raw28648step0 i j); unfold raw28648step1 raw28648step0; decide +kernel
      have hl : raw28648step1Labels = raw28648step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1875 node1875Labels := by rfl

def raw28649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28649 raw28649Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw28649 raw28649Labels = mixedMoment B raw28649step0 raw28649step0Labels := by
      have hz : ∀ j, raw28649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28649step0 = (fun i j => raw28649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28649step0 raw28649; decide +kernel
      have hl : raw28649step0Labels = raw28649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28649 raw28649Labels permutation346 hz
    mixedMoment B raw28649step0 raw28649step0Labels = mixedMoment B raw28649step1 raw28649step1Labels := by
      have ha : raw28649step1 = (fun i j => raw28649step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28649step1 raw28649step0; decide +kernel
      have hl : raw28649step1Labels = raw28649step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28649step0 raw28649step0Labels permutation145 permutation3
    mixedMoment B raw28649step1 raw28649step1Labels = mixedMoment B raw28649step2 raw28649step2Labels := by
      have ha : raw28649step2 = -raw28649step1 := by apply Matrix.ext; change ∀ i j, raw28649step2 i j = -(raw28649step1 i j); unfold raw28649step2 raw28649step1; decide +kernel
      have hl : raw28649step2Labels = raw28649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1924 node1924Labels := by rfl

def raw28650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28650step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28650 raw28650Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw28650 raw28650Labels = mixedMoment B raw28650step0 raw28650step0Labels := by
      have hz : ∀ j, raw28650 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28650step0 = (fun i j => raw28650 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28650step0 raw28650; decide +kernel
      have hl : raw28650step0Labels = raw28650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28650 raw28650Labels permutation434 hz
    mixedMoment B raw28650step0 raw28650step0Labels = mixedMoment B raw28650step1 raw28650step1Labels := by
      have hz : ∀ j, raw28650step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28650step1 = (fun i j => raw28650step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28650step1 raw28650step0; decide +kernel
      have hl : raw28650step1Labels = raw28650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28650step0 raw28650step0Labels permutation80 hz
    mixedMoment B raw28650step1 raw28650step1Labels = mixedMoment B raw28650step2 raw28650step2Labels := by
      have ha : raw28650step2 = (fun i j => raw28650step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28650step2 raw28650step1; decide +kernel
      have hl : raw28650step2Labels = raw28650step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28650step1 raw28650step1Labels permutation8 permutation3
    _ = mixedMoment B node937 node937Labels := by rfl

def raw28651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28651step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28651step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28651 raw28651Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw28651 raw28651Labels = mixedMoment B raw28651step0 raw28651step0Labels := by
      have hz : ∀ j, raw28651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28651step0 = (fun i j => raw28651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28651step0 raw28651; decide +kernel
      have hl : raw28651step0Labels = raw28651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28651 raw28651Labels permutation434 hz
    mixedMoment B raw28651step0 raw28651step0Labels = mixedMoment B raw28651step1 raw28651step1Labels := by
      have hz : ∀ j, raw28651step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28651step1 = (fun i j => raw28651step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28651step1 raw28651step0; decide +kernel
      have hl : raw28651step1Labels = raw28651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28651step0 raw28651step0Labels permutation80 hz
    mixedMoment B raw28651step1 raw28651step1Labels = mixedMoment B raw28651step2 raw28651step2Labels := by
      have ha : raw28651step2 = (fun i j => raw28651step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28651step2 raw28651step1; decide +kernel
      have hl : raw28651step2Labels = raw28651step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28651step1 raw28651step1Labels permutation31 permutation3
    mixedMoment B raw28651step2 raw28651step2Labels = mixedMoment B raw28651step3 raw28651step3Labels := by
      have ha : raw28651step3 = -raw28651step2 := by apply Matrix.ext; change ∀ i j, raw28651step3 i j = -(raw28651step2 i j); unfold raw28651step3 raw28651step2; decide +kernel
      have hl : raw28651step3Labels = raw28651step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1818 node1818Labels := by rfl

def raw28652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28652 raw28652Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw28652 raw28652Labels = mixedMoment B raw28652step0 raw28652step0Labels := by
      have hz : ∀ j, raw28652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28652step0 = (fun i j => raw28652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28652step0 raw28652; decide +kernel
      have hl : raw28652step0Labels = raw28652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28652 raw28652Labels permutation434 hz
    mixedMoment B raw28652step0 raw28652step0Labels = mixedMoment B raw28652step1 raw28652step1Labels := by
      have ha : raw28652step1 = (fun i j => raw28652step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28652step1 raw28652step0; decide +kernel
      have hl : raw28652step1Labels = raw28652step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28652step0 raw28652step0Labels permutation149 permutation3
    mixedMoment B raw28652step1 raw28652step1Labels = mixedMoment B raw28652step2 raw28652step2Labels := by
      have ha : raw28652step2 = -raw28652step1 := by apply Matrix.ext; change ∀ i j, raw28652step2 i j = -(raw28652step1 i j); unfold raw28652step2 raw28652step1; decide +kernel
      have hl : raw28652step2Labels = raw28652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1807 node1807Labels := by rfl

def raw28653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28653 raw28653Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw28653 raw28653Labels = mixedMoment B raw28653step0 raw28653step0Labels := by
      have hz : ∀ j, raw28653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28653step0 = (fun i j => raw28653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28653step0 raw28653; decide +kernel
      have hl : raw28653step0Labels = raw28653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28653 raw28653Labels permutation346 hz
    mixedMoment B raw28653step0 raw28653step0Labels = mixedMoment B raw28653step1 raw28653step1Labels := by
      have ha : raw28653step1 = (fun i j => raw28653step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28653step1 raw28653step0; decide +kernel
      have hl : raw28653step1Labels = raw28653step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28653step0 raw28653step0Labels permutation149 permutation3
    mixedMoment B raw28653step1 raw28653step1Labels = mixedMoment B raw28653step2 raw28653step2Labels := by
      have ha : raw28653step2 = -raw28653step1 := by apply Matrix.ext; change ∀ i j, raw28653step2 i j = -(raw28653step1 i j); unfold raw28653step2 raw28653step1; decide +kernel
      have hl : raw28653step2Labels = raw28653step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1807 node1807Labels := by rfl

def raw28654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28654step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28654step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28654step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28654step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28654 raw28654Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw28654 raw28654Labels = mixedMoment B raw28654step0 raw28654step0Labels := by
      have hz : ∀ j, raw28654 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28654step0 = (fun i j => raw28654 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28654step0 raw28654; decide +kernel
      have hl : raw28654step0Labels = raw28654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28654 raw28654Labels permutation434 hz
    mixedMoment B raw28654step0 raw28654step0Labels = mixedMoment B raw28654step1 raw28654step1Labels := by
      have hz : ∀ j, raw28654step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28654step1 = (fun i j => raw28654step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28654step1 raw28654step0; decide +kernel
      have hl : raw28654step1Labels = raw28654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28654step0 raw28654step0Labels permutation80 hz
    mixedMoment B raw28654step1 raw28654step1Labels = mixedMoment B raw28654step2 raw28654step2Labels := by
      have ha : raw28654step2 = (fun i j => raw28654step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28654step2 raw28654step1; decide +kernel
      have hl : raw28654step2Labels = raw28654step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28654step1 raw28654step1Labels permutation31 permutation3
    mixedMoment B raw28654step2 raw28654step2Labels = mixedMoment B raw28654step3 raw28654step3Labels := by
      have ha : raw28654step3 = -raw28654step2 := by apply Matrix.ext; change ∀ i j, raw28654step3 i j = -(raw28654step2 i j); unfold raw28654step3 raw28654step2; decide +kernel
      have hl : raw28654step3Labels = raw28654step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node735 node735Labels := by rfl

def raw28655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28655step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28655step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28655step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28655 raw28655Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw28655 raw28655Labels = mixedMoment B raw28655step0 raw28655step0Labels := by
      have hz : ∀ j, raw28655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28655step0 = (fun i j => raw28655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28655step0 raw28655; decide +kernel
      have hl : raw28655step0Labels = raw28655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28655 raw28655Labels permutation434 hz
    mixedMoment B raw28655step0 raw28655step0Labels = mixedMoment B raw28655step1 raw28655step1Labels := by
      have hz : ∀ j, raw28655step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28655step1 = (fun i j => raw28655step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28655step1 raw28655step0; decide +kernel
      have hl : raw28655step1Labels = raw28655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28655step0 raw28655step0Labels permutation80 hz
    mixedMoment B raw28655step1 raw28655step1Labels = mixedMoment B raw28655step2 raw28655step2Labels := by
      have ha : raw28655step2 = (fun i j => raw28655step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28655step2 raw28655step1; decide +kernel
      have hl : raw28655step2Labels = raw28655step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28655step1 raw28655step1Labels permutation31 permutation3
    mixedMoment B raw28655step2 raw28655step2Labels = mixedMoment B raw28655step3 raw28655step3Labels := by
      have ha : raw28655step3 = -raw28655step2 := by apply Matrix.ext; change ∀ i j, raw28655step3 i j = -(raw28655step2 i j); unfold raw28655step3 raw28655step2; decide +kernel
      have hl : raw28655step3Labels = raw28655step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node742 node742Labels := by rfl

def raw28656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28656 raw28656Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw28656 raw28656Labels = mixedMoment B raw28656step0 raw28656step0Labels := by
      have hz : ∀ j, raw28656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28656step0 = (fun i j => raw28656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28656step0 raw28656; decide +kernel
      have hl : raw28656step0Labels = raw28656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28656 raw28656Labels permutation434 hz
    mixedMoment B raw28656step0 raw28656step0Labels = mixedMoment B raw28656step1 raw28656step1Labels := by
      have ha : raw28656step1 = (fun i j => raw28656step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28656step1 raw28656step0; decide +kernel
      have hl : raw28656step1Labels = raw28656step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28656step0 raw28656step0Labels permutation149 permutation3
    mixedMoment B raw28656step1 raw28656step1Labels = mixedMoment B raw28656step2 raw28656step2Labels := by
      have ha : raw28656step2 = -raw28656step1 := by apply Matrix.ext; change ∀ i j, raw28656step2 i j = -(raw28656step1 i j); unfold raw28656step2 raw28656step1; decide +kernel
      have hl : raw28656step2Labels = raw28656step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node733 node733Labels := by rfl

def raw28657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28657 raw28657Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw28657 raw28657Labels = mixedMoment B raw28657step0 raw28657step0Labels := by
      have hz : ∀ j, raw28657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28657step0 = (fun i j => raw28657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28657step0 raw28657; decide +kernel
      have hl : raw28657step0Labels = raw28657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28657 raw28657Labels permutation346 hz
    mixedMoment B raw28657step0 raw28657step0Labels = mixedMoment B raw28657step1 raw28657step1Labels := by
      have ha : raw28657step1 = (fun i j => raw28657step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28657step1 raw28657step0; decide +kernel
      have hl : raw28657step1Labels = raw28657step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28657step0 raw28657step0Labels permutation149 permutation3
    mixedMoment B raw28657step1 raw28657step1Labels = mixedMoment B raw28657step2 raw28657step2Labels := by
      have ha : raw28657step2 = -raw28657step1 := by apply Matrix.ext; change ∀ i j, raw28657step2 i j = -(raw28657step1 i j); unfold raw28657step2 raw28657step1; decide +kernel
      have hl : raw28657step2Labels = raw28657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node733 node733Labels := by rfl

def raw28658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![4, -4, 0]]
def raw28658step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28658step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28658 raw28658Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw28658 raw28658Labels = mixedMoment B raw28658step0 raw28658step0Labels := by
      have hz : ∀ j, raw28658 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28658step0 = (fun i j => raw28658 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28658step0 raw28658; decide +kernel
      have hl : raw28658step0Labels = raw28658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28658 raw28658Labels permutation434 hz
    mixedMoment B raw28658step0 raw28658step0Labels = mixedMoment B raw28658step1 raw28658step1Labels := by
      have hz : ∀ j, raw28658step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28658step1 = (fun i j => raw28658step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28658step1 raw28658step0; decide +kernel
      have hl : raw28658step1Labels = raw28658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28658step0 raw28658step0Labels permutation80 hz
    mixedMoment B raw28658step1 raw28658step1Labels = mixedMoment B raw28658step2 raw28658step2Labels := by
      have ha : raw28658step2 = (fun i j => raw28658step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28658step2 raw28658step1; decide +kernel
      have hl : raw28658step2Labels = raw28658step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28658step1 raw28658step1Labels permutation31 permutation3
    mixedMoment B raw28658step2 raw28658step2Labels = mixedMoment B raw28658step3 raw28658step3Labels := by
      have ha : raw28658step3 = -raw28658step2 := by apply Matrix.ext; change ∀ i j, raw28658step3 i j = -(raw28658step2 i j); unfold raw28658step3 raw28658step2; decide +kernel
      have hl : raw28658step3Labels = raw28658step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node826 node826Labels := by rfl

def raw28659 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 1, 1], ![0, -3, 3]]
def raw28659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28659step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28659step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28659step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28659step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28659 raw28659Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw28659 raw28659Labels = mixedMoment B raw28659step0 raw28659step0Labels := by
      have hz : ∀ j, raw28659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28659step0 = (fun i j => raw28659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28659step0 raw28659; decide +kernel
      have hl : raw28659step0Labels = raw28659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28659 raw28659Labels permutation434 hz
    mixedMoment B raw28659step0 raw28659step0Labels = mixedMoment B raw28659step1 raw28659step1Labels := by
      have hz : ∀ j, raw28659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28659step1 = (fun i j => raw28659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28659step1 raw28659step0; decide +kernel
      have hl : raw28659step1Labels = raw28659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28659step0 raw28659step0Labels permutation80 hz
    mixedMoment B raw28659step1 raw28659step1Labels = mixedMoment B raw28659step2 raw28659step2Labels := by
      have ha : raw28659step2 = (fun i j => raw28659step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28659step2 raw28659step1; decide +kernel
      have hl : raw28659step2Labels = raw28659step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28659step1 raw28659step1Labels permutation31 permutation6
    mixedMoment B raw28659step2 raw28659step2Labels = mixedMoment B raw28659step3 raw28659step3Labels := by
      have ha : raw28659step3 = -raw28659step2 := by apply Matrix.ext; change ∀ i j, raw28659step3 i j = -(raw28659step2 i j); unfold raw28659step3 raw28659step2; decide +kernel
      have hl : raw28659step3Labels = raw28659step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28659step3 raw28659step3Labels = mixedMoment B raw28659step4 raw28659step4Labels := by
      have ha : raw28659step4 = raw28659step3 := by apply Matrix.ext; unfold raw28659step4 raw28659step3; decide +kernel
      have hl : raw28659step3Labels = labelEmbedding9 ∘ raw28659step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28659step3 raw28659step3Labels raw28659step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw28660 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw28660step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28660step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28660step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28660step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28660 raw28660Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw28660 raw28660Labels = mixedMoment B raw28660step0 raw28660step0Labels := by
      have hz : ∀ j, raw28660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28660step0 = (fun i j => raw28660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28660step0 raw28660; decide +kernel
      have hl : raw28660step0Labels = raw28660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28660 raw28660Labels permutation434 hz
    mixedMoment B raw28660step0 raw28660step0Labels = mixedMoment B raw28660step1 raw28660step1Labels := by
      have ha : raw28660step1 = (fun i j => raw28660step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28660step1 raw28660step0; decide +kernel
      have hl : raw28660step1Labels = raw28660step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28660step0 raw28660step0Labels permutation151 permutation6
    mixedMoment B raw28660step1 raw28660step1Labels = mixedMoment B raw28660step2 raw28660step2Labels := by
      have ha : raw28660step2 = -raw28660step1 := by apply Matrix.ext; change ∀ i j, raw28660step2 i j = -(raw28660step1 i j); unfold raw28660step2 raw28660step1; decide +kernel
      have hl : raw28660step2Labels = raw28660step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28660step2 raw28660step2Labels = mixedMoment B raw28660step3 raw28660step3Labels := by
      have ha : raw28660step3 = raw28660step2 := by apply Matrix.ext; unfold raw28660step3 raw28660step2; decide +kernel
      have hl : raw28660step2Labels = labelEmbedding9 ∘ raw28660step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28660step2 raw28660step2Labels raw28660step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw28661 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw28661step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28661step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28661step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28661step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28661 raw28661Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw28661 raw28661Labels = mixedMoment B raw28661step0 raw28661step0Labels := by
      have hz : ∀ j, raw28661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28661step0 = (fun i j => raw28661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28661step0 raw28661; decide +kernel
      have hl : raw28661step0Labels = raw28661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28661 raw28661Labels permutation346 hz
    mixedMoment B raw28661step0 raw28661step0Labels = mixedMoment B raw28661step1 raw28661step1Labels := by
      have ha : raw28661step1 = (fun i j => raw28661step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28661step1 raw28661step0; decide +kernel
      have hl : raw28661step1Labels = raw28661step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28661step0 raw28661step0Labels permutation151 permutation6
    mixedMoment B raw28661step1 raw28661step1Labels = mixedMoment B raw28661step2 raw28661step2Labels := by
      have ha : raw28661step2 = -raw28661step1 := by apply Matrix.ext; change ∀ i j, raw28661step2 i j = -(raw28661step1 i j); unfold raw28661step2 raw28661step1; decide +kernel
      have hl : raw28661step2Labels = raw28661step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28661step2 raw28661step2Labels = mixedMoment B raw28661step3 raw28661step3Labels := by
      have ha : raw28661step3 = raw28661step2 := by apply Matrix.ext; unfold raw28661step3 raw28661step2; decide +kernel
      have hl : raw28661step2Labels = labelEmbedding9 ∘ raw28661step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28661step2 raw28661step2Labels raw28661step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw28662 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-3, 2, 1], ![0, -3, 3]]
def raw28662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28662step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28662step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28662step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28662step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28662 raw28662Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw28662 raw28662Labels = mixedMoment B raw28662step0 raw28662step0Labels := by
      have hz : ∀ j, raw28662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28662step0 = (fun i j => raw28662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28662step0 raw28662; decide +kernel
      have hl : raw28662step0Labels = raw28662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28662 raw28662Labels permutation434 hz
    mixedMoment B raw28662step0 raw28662step0Labels = mixedMoment B raw28662step1 raw28662step1Labels := by
      have hz : ∀ j, raw28662step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28662step1 = (fun i j => raw28662step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28662step1 raw28662step0; decide +kernel
      have hl : raw28662step1Labels = raw28662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28662step0 raw28662step0Labels permutation80 hz
    mixedMoment B raw28662step1 raw28662step1Labels = mixedMoment B raw28662step2 raw28662step2Labels := by
      have ha : raw28662step2 = (fun i j => raw28662step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28662step2 raw28662step1; decide +kernel
      have hl : raw28662step2Labels = raw28662step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28662step1 raw28662step1Labels permutation31 permutation6
    mixedMoment B raw28662step2 raw28662step2Labels = mixedMoment B raw28662step3 raw28662step3Labels := by
      have ha : raw28662step3 = -raw28662step2 := by apply Matrix.ext; change ∀ i j, raw28662step3 i j = -(raw28662step2 i j); unfold raw28662step3 raw28662step2; decide +kernel
      have hl : raw28662step3Labels = raw28662step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28662step3 raw28662step3Labels = mixedMoment B raw28662step4 raw28662step4Labels := by
      have ha : raw28662step4 = raw28662step3 := by apply Matrix.ext; unfold raw28662step4 raw28662step3; decide +kernel
      have hl : raw28662step3Labels = labelEmbedding9 ∘ raw28662step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28662step3 raw28662step3Labels raw28662step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw28663 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 1, 1], ![-1, -2, 3]]
def raw28663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28663step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28663 raw28663Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw28663 raw28663Labels = mixedMoment B raw28663step0 raw28663step0Labels := by
      have hz : ∀ j, raw28663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28663step0 = (fun i j => raw28663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28663step0 raw28663; decide +kernel
      have hl : raw28663step0Labels = raw28663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28663 raw28663Labels permutation434 hz
    mixedMoment B raw28663step0 raw28663step0Labels = mixedMoment B raw28663step1 raw28663step1Labels := by
      have hz : ∀ j, raw28663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28663step1 = (fun i j => raw28663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28663step1 raw28663step0; decide +kernel
      have hl : raw28663step1Labels = raw28663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28663step0 raw28663step0Labels permutation80 hz
    mixedMoment B raw28663step1 raw28663step1Labels = mixedMoment B raw28663step2 raw28663step2Labels := by
      have ha : raw28663step2 = (fun i j => raw28663step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28663step2 raw28663step1; decide +kernel
      have hl : raw28663step2Labels = raw28663step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28663step1 raw28663step1Labels permutation8 permutation7
    mixedMoment B raw28663step2 raw28663step2Labels = mixedMoment B raw28663step3 raw28663step3Labels := by
      have ha : raw28663step3 = raw28663step2 := by apply Matrix.ext; unfold raw28663step3 raw28663step2; decide +kernel
      have hl : raw28663step2Labels = labelEmbedding10 ∘ raw28663step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28663step2 raw28663step2Labels raw28663step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw28664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 1, 1], ![0, -3, 3]]
def raw28664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28664step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28664step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28664 raw28664Labels = mixedMoment B node4862 node4862Labels := by
  calc
    mixedMoment B raw28664 raw28664Labels = mixedMoment B raw28664step0 raw28664step0Labels := by
      have hz : ∀ j, raw28664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28664step0 = (fun i j => raw28664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28664step0 raw28664; decide +kernel
      have hl : raw28664step0Labels = raw28664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28664 raw28664Labels permutation434 hz
    mixedMoment B raw28664step0 raw28664step0Labels = mixedMoment B raw28664step1 raw28664step1Labels := by
      have hz : ∀ j, raw28664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28664step1 = (fun i j => raw28664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28664step1 raw28664step0; decide +kernel
      have hl : raw28664step1Labels = raw28664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28664step0 raw28664step0Labels permutation80 hz
    mixedMoment B raw28664step1 raw28664step1Labels = mixedMoment B raw28664step2 raw28664step2Labels := by
      have ha : raw28664step2 = (fun i j => raw28664step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28664step2 raw28664step1; decide +kernel
      have hl : raw28664step2Labels = raw28664step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28664step1 raw28664step1Labels permutation29 permutation4
    mixedMoment B raw28664step2 raw28664step2Labels = mixedMoment B raw28664step3 raw28664step3Labels := by
      have ha : raw28664step3 = raw28664step2 := by apply Matrix.ext; unfold raw28664step3 raw28664step2; decide +kernel
      have hl : raw28664step2Labels = labelEmbedding7 ∘ raw28664step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28664step2 raw28664step2Labels raw28664step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4862 node4862Labels := by rfl

def raw28665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw28665step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28665step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28665 raw28665Labels = mixedMoment B node4850 node4850Labels := by
  calc
    mixedMoment B raw28665 raw28665Labels = mixedMoment B raw28665step0 raw28665step0Labels := by
      have hz : ∀ j, raw28665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28665step0 = (fun i j => raw28665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28665step0 raw28665; decide +kernel
      have hl : raw28665step0Labels = raw28665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28665 raw28665Labels permutation434 hz
    mixedMoment B raw28665step0 raw28665step0Labels = mixedMoment B raw28665step1 raw28665step1Labels := by
      have ha : raw28665step1 = (fun i j => raw28665step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28665step1 raw28665step0; decide +kernel
      have hl : raw28665step1Labels = raw28665step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28665step0 raw28665step0Labels permutation151 permutation6
    mixedMoment B raw28665step1 raw28665step1Labels = mixedMoment B raw28665step2 raw28665step2Labels := by
      have ha : raw28665step2 = -raw28665step1 := by apply Matrix.ext; change ∀ i j, raw28665step2 i j = -(raw28665step1 i j); unfold raw28665step2 raw28665step1; decide +kernel
      have hl : raw28665step2Labels = raw28665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28665step2 raw28665step2Labels = mixedMoment B raw28665step3 raw28665step3Labels := by
      have ha : raw28665step3 = raw28665step2 := by apply Matrix.ext; unfold raw28665step3 raw28665step2; decide +kernel
      have hl : raw28665step2Labels = labelEmbedding9 ∘ raw28665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28665step2 raw28665step2Labels raw28665step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4850 node4850Labels := by rfl

def raw28666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw28666step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28666step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28666 raw28666Labels = mixedMoment B node4850 node4850Labels := by
  calc
    mixedMoment B raw28666 raw28666Labels = mixedMoment B raw28666step0 raw28666step0Labels := by
      have hz : ∀ j, raw28666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28666step0 = (fun i j => raw28666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28666step0 raw28666; decide +kernel
      have hl : raw28666step0Labels = raw28666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28666 raw28666Labels permutation346 hz
    mixedMoment B raw28666step0 raw28666step0Labels = mixedMoment B raw28666step1 raw28666step1Labels := by
      have ha : raw28666step1 = (fun i j => raw28666step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28666step1 raw28666step0; decide +kernel
      have hl : raw28666step1Labels = raw28666step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28666step0 raw28666step0Labels permutation151 permutation6
    mixedMoment B raw28666step1 raw28666step1Labels = mixedMoment B raw28666step2 raw28666step2Labels := by
      have ha : raw28666step2 = -raw28666step1 := by apply Matrix.ext; change ∀ i j, raw28666step2 i j = -(raw28666step1 i j); unfold raw28666step2 raw28666step1; decide +kernel
      have hl : raw28666step2Labels = raw28666step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28666step2 raw28666step2Labels = mixedMoment B raw28666step3 raw28666step3Labels := by
      have ha : raw28666step3 = raw28666step2 := by apply Matrix.ext; unfold raw28666step3 raw28666step2; decide +kernel
      have hl : raw28666step2Labels = labelEmbedding9 ∘ raw28666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28666step2 raw28666step2Labels raw28666step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4850 node4850Labels := by rfl

def raw28667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-3, 2, 1], ![0, -3, 3]]
def raw28667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw28667step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw28667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28667 raw28667Labels = mixedMoment B node4873 node4873Labels := by
  calc
    mixedMoment B raw28667 raw28667Labels = mixedMoment B raw28667step0 raw28667step0Labels := by
      have hz : ∀ j, raw28667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28667step0 = (fun i j => raw28667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28667step0 raw28667; decide +kernel
      have hl : raw28667step0Labels = raw28667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28667 raw28667Labels permutation434 hz
    mixedMoment B raw28667step0 raw28667step0Labels = mixedMoment B raw28667step1 raw28667step1Labels := by
      have hz : ∀ j, raw28667step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28667step1 = (fun i j => raw28667step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28667step1 raw28667step0; decide +kernel
      have hl : raw28667step1Labels = raw28667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28667step0 raw28667step0Labels permutation80 hz
    mixedMoment B raw28667step1 raw28667step1Labels = mixedMoment B raw28667step2 raw28667step2Labels := by
      have ha : raw28667step2 = (fun i j => raw28667step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28667step2 raw28667step1; decide +kernel
      have hl : raw28667step2Labels = raw28667step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28667step1 raw28667step1Labels permutation29 permutation4
    mixedMoment B raw28667step2 raw28667step2Labels = mixedMoment B raw28667step3 raw28667step3Labels := by
      have ha : raw28667step3 = raw28667step2 := by apply Matrix.ext; unfold raw28667step3 raw28667step2; decide +kernel
      have hl : raw28667step2Labels = labelEmbedding7 ∘ raw28667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28667step2 raw28667step2Labels raw28667step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4873 node4873Labels := by rfl

def raw28668 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 1, 1], ![-1, -2, 3]]
def raw28668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28668step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28668 raw28668Labels = mixedMoment B node5201 node5201Labels := by
  calc
    mixedMoment B raw28668 raw28668Labels = mixedMoment B raw28668step0 raw28668step0Labels := by
      have hz : ∀ j, raw28668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28668step0 = (fun i j => raw28668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28668step0 raw28668; decide +kernel
      have hl : raw28668step0Labels = raw28668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28668 raw28668Labels permutation434 hz
    mixedMoment B raw28668step0 raw28668step0Labels = mixedMoment B raw28668step1 raw28668step1Labels := by
      have hz : ∀ j, raw28668step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28668step1 = (fun i j => raw28668step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28668step1 raw28668step0; decide +kernel
      have hl : raw28668step1Labels = raw28668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28668step0 raw28668step0Labels permutation80 hz
    mixedMoment B raw28668step1 raw28668step1Labels = mixedMoment B raw28668step2 raw28668step2Labels := by
      have ha : raw28668step2 = (fun i j => raw28668step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28668step2 raw28668step1; decide +kernel
      have hl : raw28668step2Labels = raw28668step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28668step1 raw28668step1Labels permutation8 permutation6
    mixedMoment B raw28668step2 raw28668step2Labels = mixedMoment B raw28668step3 raw28668step3Labels := by
      have ha : raw28668step3 = raw28668step2 := by apply Matrix.ext; unfold raw28668step3 raw28668step2; decide +kernel
      have hl : raw28668step2Labels = labelEmbedding9 ∘ raw28668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28668step2 raw28668step2Labels raw28668step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5201 node5201Labels := by rfl

def raw28669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28669step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28669 raw28669Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw28669 raw28669Labels = mixedMoment B raw28669step0 raw28669step0Labels := by
      have hz : ∀ j, raw28669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28669step0 = (fun i j => raw28669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28669step0 raw28669; decide +kernel
      have hl : raw28669step0Labels = raw28669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28669 raw28669Labels permutation434 hz
    mixedMoment B raw28669step0 raw28669step0Labels = mixedMoment B raw28669step1 raw28669step1Labels := by
      have ha : raw28669step1 = (fun i j => raw28669step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28669step1 raw28669step0; decide +kernel
      have hl : raw28669step1Labels = raw28669step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28669step0 raw28669step0Labels permutation143 permutation4
    mixedMoment B raw28669step1 raw28669step1Labels = mixedMoment B raw28669step2 raw28669step2Labels := by
      have ha : raw28669step2 = raw28669step1 := by apply Matrix.ext; unfold raw28669step2 raw28669step1; decide +kernel
      have hl : raw28669step1Labels = labelEmbedding7 ∘ raw28669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28669step1 raw28669step1Labels raw28669step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

def raw28670 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28670 raw28670Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw28670 raw28670Labels = mixedMoment B raw28670step0 raw28670step0Labels := by
      have hz : ∀ j, raw28670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28670step0 = (fun i j => raw28670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28670step0 raw28670; decide +kernel
      have hl : raw28670step0Labels = raw28670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28670 raw28670Labels permutation434 hz
    mixedMoment B raw28670step0 raw28670step0Labels = mixedMoment B raw28670step1 raw28670step1Labels := by
      have ha : raw28670step1 = (fun i j => raw28670step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28670step1 raw28670step0; decide +kernel
      have hl : raw28670step1Labels = raw28670step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28670step0 raw28670step0Labels permutation145 permutation4
    mixedMoment B raw28670step1 raw28670step1Labels = mixedMoment B raw28670step2 raw28670step2Labels := by
      have ha : raw28670step2 = raw28670step1 := by apply Matrix.ext; unfold raw28670step2 raw28670step1; decide +kernel
      have hl : raw28670step1Labels = labelEmbedding7 ∘ raw28670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28670step1 raw28670step1Labels raw28670step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw28671 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28671step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28671 raw28671Labels = mixedMoment B node4797 node4797Labels := by
  calc
    mixedMoment B raw28671 raw28671Labels = mixedMoment B raw28671step0 raw28671step0Labels := by
      have ha : raw28671step0 = (fun i j => raw28671 (permutation634 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28671step0 raw28671; decide +kernel
      have hl : raw28671step0Labels = raw28671Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28671 raw28671Labels permutation634 permutation4
    mixedMoment B raw28671step0 raw28671step0Labels = mixedMoment B raw28671step1 raw28671step1Labels := by
      have ha : raw28671step1 = raw28671step0 := by apply Matrix.ext; unfold raw28671step1 raw28671step0; decide +kernel
      have hl : raw28671step0Labels = labelEmbedding7 ∘ raw28671step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28671step0 raw28671step0Labels raw28671step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4797 node4797Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
