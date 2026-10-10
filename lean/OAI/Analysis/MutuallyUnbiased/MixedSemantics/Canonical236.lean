import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30208 raw30208Labels = mixedMoment B node2007 node2007Labels := by
  calc
    mixedMoment B raw30208 raw30208Labels = mixedMoment B raw30208step0 raw30208step0Labels := by
      have hz : ∀ j, raw30208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30208step0 = (fun i j => raw30208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30208step0 raw30208; decide +kernel
      have hl : raw30208step0Labels = raw30208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30208 raw30208Labels permutation434 hz
    mixedMoment B raw30208step0 raw30208step0Labels = mixedMoment B raw30208step1 raw30208step1Labels := by
      have ha : raw30208step1 = (fun i j => raw30208step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30208step1 raw30208step0; decide +kernel
      have hl : raw30208step1Labels = raw30208step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30208step0 raw30208step0Labels permutation38 permutation4
    mixedMoment B raw30208step1 raw30208step1Labels = mixedMoment B raw30208step2 raw30208step2Labels := by
      have ha : raw30208step2 = -raw30208step1 := by apply Matrix.ext; change ∀ i j, raw30208step2 i j = -(raw30208step1 i j); unfold raw30208step2 raw30208step1; decide +kernel
      have hl : raw30208step2Labels = raw30208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2007 node2007Labels := by rfl

def raw30209 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw30209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30209 raw30209Labels = mixedMoment B node1954 node1954Labels := by
  calc
    mixedMoment B raw30209 raw30209Labels = mixedMoment B raw30209step0 raw30209step0Labels := by
      have ha : raw30209step0 = (fun i j => raw30209 (permutation183 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30209step0 raw30209; decide +kernel
      have hl : raw30209step0Labels = raw30209Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30209 raw30209Labels permutation183 permutation4
    mixedMoment B raw30209step0 raw30209step0Labels = mixedMoment B raw30209step1 raw30209step1Labels := by
      have ha : raw30209step1 = -raw30209step0 := by apply Matrix.ext; change ∀ i j, raw30209step1 i j = -(raw30209step0 i j); unfold raw30209step1 raw30209step0; decide +kernel
      have hl : raw30209step1Labels = raw30209step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1954 node1954Labels := by rfl

def raw30210 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw30210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30210 raw30210Labels = mixedMoment B node1954 node1954Labels := by
  calc
    mixedMoment B raw30210 raw30210Labels = mixedMoment B raw30210step0 raw30210step0Labels := by
      have ha : raw30210step0 = (fun i j => raw30210 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30210step0 raw30210; decide +kernel
      have hl : raw30210step0Labels = raw30210Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30210 raw30210Labels permutation182 permutation4
    mixedMoment B raw30210step0 raw30210step0Labels = mixedMoment B raw30210step1 raw30210step1Labels := by
      have ha : raw30210step1 = -raw30210step0 := by apply Matrix.ext; change ∀ i j, raw30210step1 i j = -(raw30210step0 i j); unfold raw30210step1 raw30210step0; decide +kernel
      have hl : raw30210step1Labels = raw30210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1954 node1954Labels := by rfl

def raw30211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw30211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, 0, -2], ![2, -3, 1]]
def raw30211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw30211step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30211 raw30211Labels = mixedMoment B node2498 node2498Labels := by
  calc
    mixedMoment B raw30211 raw30211Labels = mixedMoment B raw30211step0 raw30211step0Labels := by
      have hz : ∀ j, raw30211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30211step0 = (fun i j => raw30211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30211step0 raw30211; decide +kernel
      have hl : raw30211step0Labels = raw30211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30211 raw30211Labels permutation434 hz
    mixedMoment B raw30211step0 raw30211step0Labels = mixedMoment B raw30211step1 raw30211step1Labels := by
      have ha : raw30211step1 = (fun i j => raw30211step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30211step1 raw30211step0; decide +kernel
      have hl : raw30211step1Labels = raw30211step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30211step0 raw30211step0Labels permutation33 permutation2
    _ = mixedMoment B node2498 node2498Labels := by rfl

def raw30212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw30212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, 0, -2], ![2, -3, 1]]
def raw30212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30212 raw30212Labels = mixedMoment B node3042 node3042Labels := by
  calc
    mixedMoment B raw30212 raw30212Labels = mixedMoment B raw30212step0 raw30212step0Labels := by
      have hz : ∀ j, raw30212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30212step0 = (fun i j => raw30212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30212step0 raw30212; decide +kernel
      have hl : raw30212step0Labels = raw30212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30212 raw30212Labels permutation434 hz
    mixedMoment B raw30212step0 raw30212step0Labels = mixedMoment B raw30212step1 raw30212step1Labels := by
      have ha : raw30212step1 = (fun i j => raw30212step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30212step1 raw30212step0; decide +kernel
      have hl : raw30212step1Labels = raw30212step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30212step0 raw30212step0Labels permutation132 permutation4
    _ = mixedMoment B node3042 node3042Labels := by rfl

def raw30213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 3, -2], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw30213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 3, -2], ![2, 0, -2], ![2, -3, 1]]
def raw30213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw30213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw30213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30213 raw30213Labels = mixedMoment B node2667 node2667Labels := by
  calc
    mixedMoment B raw30213 raw30213Labels = mixedMoment B raw30213step0 raw30213step0Labels := by
      have hz : ∀ j, raw30213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30213step0 = (fun i j => raw30213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30213step0 raw30213; decide +kernel
      have hl : raw30213step0Labels = raw30213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30213 raw30213Labels permutation434 hz
    mixedMoment B raw30213step0 raw30213step0Labels = mixedMoment B raw30213step1 raw30213step1Labels := by
      have ha : raw30213step1 = (fun i j => raw30213step0 (permutation94 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30213step1 raw30213step0; decide +kernel
      have hl : raw30213step1Labels = raw30213step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30213step0 raw30213step0Labels permutation94 permutation4
    mixedMoment B raw30213step1 raw30213step1Labels = mixedMoment B raw30213step2 raw30213step2Labels := by
      have ha : raw30213step2 = -raw30213step1 := by apply Matrix.ext; change ∀ i j, raw30213step2 i j = -(raw30213step1 i j); unfold raw30213step2 raw30213step1; decide +kernel
      have hl : raw30213step2Labels = raw30213step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2667 node2667Labels := by rfl

def raw30214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw30214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30214 raw30214Labels = mixedMoment B node3018 node3018Labels := by
  calc
    mixedMoment B raw30214 raw30214Labels = mixedMoment B raw30214step0 raw30214step0Labels := by
      have ha : raw30214step0 = (fun i j => raw30214 (permutation594 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30214step0 raw30214; decide +kernel
      have hl : raw30214step0Labels = raw30214Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30214 raw30214Labels permutation594 permutation4
    _ = mixedMoment B node3018 node3018Labels := by rfl

def raw30215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw30215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw30215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30215 raw30215Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw30215 raw30215Labels = mixedMoment B raw30215step0 raw30215step0Labels := by
      have hz : ∀ j, raw30215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30215step0 = (fun i j => raw30215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30215step0 raw30215; decide +kernel
      have hl : raw30215step0Labels = raw30215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30215 raw30215Labels permutation434 hz
    mixedMoment B raw30215step0 raw30215step0Labels = mixedMoment B raw30215step1 raw30215step1Labels := by
      have ha : raw30215step1 = (fun i j => raw30215step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30215step1 raw30215step0; decide +kernel
      have hl : raw30215step1Labels = raw30215step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30215step0 raw30215step0Labels permutation129 permutation4
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw30216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw30216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![2, 0, -2], ![1, -2, 1]]
def raw30216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30216 raw30216Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw30216 raw30216Labels = mixedMoment B raw30216step0 raw30216step0Labels := by
      have hz : ∀ j, raw30216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30216step0 = (fun i j => raw30216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30216step0 raw30216; decide +kernel
      have hl : raw30216step0Labels = raw30216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30216 raw30216Labels permutation434 hz
    mixedMoment B raw30216step0 raw30216step0Labels = mixedMoment B raw30216step1 raw30216step1Labels := by
      have ha : raw30216step1 = (fun i j => raw30216step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30216step1 raw30216step0; decide +kernel
      have hl : raw30216step1Labels = raw30216step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30216step0 raw30216step0Labels permutation33 permutation2
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw30217 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![0, 0], ![2, -2], ![-1, 1]]
def raw30217Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30217step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![2, -2], ![-1, 1]]
def raw30217step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30217step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw30217step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30217step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30217step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30217 raw30217Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30217 raw30217Labels = mixedMoment B raw30217step0 raw30217step0Labels := by
      have hz : ∀ j, raw30217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30217step0 = (fun i j => raw30217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30217step0 raw30217; decide +kernel
      have hl : raw30217step0Labels = raw30217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30217 raw30217Labels permutation434 hz
    mixedMoment B raw30217step0 raw30217step0Labels = mixedMoment B raw30217step1 raw30217step1Labels := by
      have ha : raw30217step1 = (fun i j => raw30217step0 (permutation95 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30217step1 raw30217step0; decide +kernel
      have hl : raw30217step1Labels = raw30217step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30217step0 raw30217step0Labels permutation95 permutation0
    mixedMoment B raw30217step1 raw30217step1Labels = mixedMoment B raw30217step2 raw30217step2Labels := by
      have ha : raw30217step2 = -raw30217step1 := by apply Matrix.ext; change ∀ i j, raw30217step2 i j = -(raw30217step1 i j); unfold raw30217step2 raw30217step1; decide +kernel
      have hl : raw30217step2Labels = raw30217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw30218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30218 raw30218Labels = mixedMoment B node2456 node2456Labels := by
  calc
    mixedMoment B raw30218 raw30218Labels = mixedMoment B raw30218step0 raw30218step0Labels := by
      have ha : raw30218step0 = (fun i j => raw30218 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30218step0 raw30218; decide +kernel
      have hl : raw30218step0Labels = raw30218Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30218 raw30218Labels permutation158 permutation2
    _ = mixedMoment B node2456 node2456Labels := by rfl

def raw30219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30219 raw30219Labels = mixedMoment B node3680 node3680Labels := by
  calc
    mixedMoment B raw30219 raw30219Labels = mixedMoment B raw30219step0 raw30219step0Labels := by
      have ha : raw30219step0 = (fun i j => raw30219 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30219step0 raw30219; decide +kernel
      have hl : raw30219step0Labels = raw30219Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30219 raw30219Labels permutation158 permutation2
    _ = mixedMoment B node3680 node3680Labels := by rfl

def raw30220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1], ![-1, 0, 1]]
def raw30220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw30220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30220 raw30220Labels = mixedMoment B node2756 node2756Labels := by
  calc
    mixedMoment B raw30220 raw30220Labels = mixedMoment B raw30220step0 raw30220step0Labels := by
      have ha : raw30220step0 = (fun i j => raw30220 (permutation369 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30220step0 raw30220; decide +kernel
      have hl : raw30220step0Labels = raw30220Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30220 raw30220Labels permutation369 permutation4
    mixedMoment B raw30220step0 raw30220step0Labels = mixedMoment B raw30220step1 raw30220step1Labels := by
      have ha : raw30220step1 = -raw30220step0 := by apply Matrix.ext; change ∀ i j, raw30220step1 i j = -(raw30220step0 i j); unfold raw30220step1 raw30220step0; decide +kernel
      have hl : raw30220step1Labels = raw30220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2756 node2756Labels := by rfl

def raw30221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30221 raw30221Labels = mixedMoment B node3776 node3776Labels := by
  calc
    mixedMoment B raw30221 raw30221Labels = mixedMoment B raw30221step0 raw30221step0Labels := by
      have ha : raw30221step0 = (fun i j => raw30221 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30221step0 raw30221; decide +kernel
      have hl : raw30221step0Labels = raw30221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30221 raw30221Labels permutation158 permutation2
    _ = mixedMoment B node3776 node3776Labels := by rfl

def raw30222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30222 raw30222Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw30222 raw30222Labels = mixedMoment B raw30222step0 raw30222step0Labels := by
      have ha : raw30222step0 = (fun i j => raw30222 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30222step0 raw30222; decide +kernel
      have hl : raw30222step0Labels = raw30222Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30222 raw30222Labels permutation158 permutation2
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw30223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30223 raw30223Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw30223 raw30223Labels = mixedMoment B raw30223step0 raw30223step0Labels := by
      have ha : raw30223step0 = (fun i j => raw30223 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30223step0 raw30223; decide +kernel
      have hl : raw30223step0Labels = raw30223Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30223 raw30223Labels permutation159 permutation2
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw30224 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw30224Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30224step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw30224step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30224 raw30224Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw30224 raw30224Labels = mixedMoment B raw30224step0 raw30224step0Labels := by
      have ha : raw30224step0 = (fun i j => raw30224 (permutation161 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30224step0 raw30224; decide +kernel
      have hl : raw30224step0Labels = raw30224Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30224 raw30224Labels permutation161 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw30225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw30225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30225 raw30225Labels = mixedMoment B node2472 node2472Labels := by
  calc
    mixedMoment B raw30225 raw30225Labels = mixedMoment B raw30225step0 raw30225step0Labels := by
      have ha : raw30225step0 = (fun i j => raw30225 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30225step0 raw30225; decide +kernel
      have hl : raw30225step0Labels = raw30225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30225 raw30225Labels permutation153 permutation2
    _ = mixedMoment B node2472 node2472Labels := by rfl

def raw30226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw30226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw30226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30226 raw30226Labels = mixedMoment B node3041 node3041Labels := by
  calc
    mixedMoment B raw30226 raw30226Labels = mixedMoment B raw30226step0 raw30226step0Labels := by
      have ha : raw30226step0 = (fun i j => raw30226 (permutation599 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30226step0 raw30226; decide +kernel
      have hl : raw30226step0Labels = raw30226Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30226 raw30226Labels permutation599 permutation4
    _ = mixedMoment B node3041 node3041Labels := by rfl

def raw30227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw30227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30227 raw30227Labels = mixedMoment B node3019 node3019Labels := by
  calc
    mixedMoment B raw30227 raw30227Labels = mixedMoment B raw30227step0 raw30227step0Labels := by
      have ha : raw30227step0 = (fun i j => raw30227 (permutation594 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30227step0 raw30227; decide +kernel
      have hl : raw30227step0Labels = raw30227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30227 raw30227Labels permutation594 permutation4
    _ = mixedMoment B node3019 node3019Labels := by rfl

def raw30228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw30228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30228 raw30228Labels = mixedMoment B node3019 node3019Labels := by
  calc
    mixedMoment B raw30228 raw30228Labels = mixedMoment B raw30228step0 raw30228step0Labels := by
      have ha : raw30228step0 = (fun i j => raw30228 (permutation593 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30228step0 raw30228; decide +kernel
      have hl : raw30228step0Labels = raw30228Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30228 raw30228Labels permutation593 permutation4
    _ = mixedMoment B node3019 node3019Labels := by rfl

def raw30229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw30229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30229 raw30229Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw30229 raw30229Labels = mixedMoment B raw30229step0 raw30229step0Labels := by
      have ha : raw30229step0 = (fun i j => raw30229 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30229step0 raw30229; decide +kernel
      have hl : raw30229step0Labels = raw30229Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30229 raw30229Labels permutation590 permutation4
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw30230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw30230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30230 raw30230Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw30230 raw30230Labels = mixedMoment B raw30230step0 raw30230step0Labels := by
      have ha : raw30230step0 = (fun i j => raw30230 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30230step0 raw30230; decide +kernel
      have hl : raw30230step0Labels = raw30230Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30230 raw30230Labels permutation153 permutation2
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw30231 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![2, -2], ![-1, 1]]
def raw30231Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30231step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw30231step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30231 raw30231Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw30231 raw30231Labels = mixedMoment B raw30231step0 raw30231step0Labels := by
      have ha : raw30231step0 = (fun i j => raw30231 (permutation170 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30231step0 raw30231; decide +kernel
      have hl : raw30231step0Labels = raw30231Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30231 raw30231Labels permutation170 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw30232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw30232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 1, -3], ![2, -3, 1]]
def raw30232step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw30232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30232 raw30232Labels = mixedMoment B node2487 node2487Labels := by
  calc
    mixedMoment B raw30232 raw30232Labels = mixedMoment B raw30232step0 raw30232step0Labels := by
      have hz : ∀ j, raw30232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30232step0 = (fun i j => raw30232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30232step0 raw30232; decide +kernel
      have hl : raw30232step0Labels = raw30232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30232 raw30232Labels permutation434 hz
    mixedMoment B raw30232step0 raw30232step0Labels = mixedMoment B raw30232step1 raw30232step1Labels := by
      have ha : raw30232step1 = (fun i j => raw30232step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30232step1 raw30232step0; decide +kernel
      have hl : raw30232step1Labels = raw30232step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30232step0 raw30232step0Labels permutation33 permutation2
    _ = mixedMoment B node2487 node2487Labels := by rfl

def raw30233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw30233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 1, -3], ![2, -3, 1]]
def raw30233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw30233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30233 raw30233Labels = mixedMoment B node3047 node3047Labels := by
  calc
    mixedMoment B raw30233 raw30233Labels = mixedMoment B raw30233step0 raw30233step0Labels := by
      have hz : ∀ j, raw30233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30233step0 = (fun i j => raw30233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30233step0 raw30233; decide +kernel
      have hl : raw30233step0Labels = raw30233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30233 raw30233Labels permutation434 hz
    mixedMoment B raw30233step0 raw30233step0Labels = mixedMoment B raw30233step1 raw30233step1Labels := by
      have ha : raw30233step1 = (fun i j => raw30233step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30233step1 raw30233step0; decide +kernel
      have hl : raw30233step1Labels = raw30233step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30233step0 raw30233step0Labels permutation128 permutation4
    _ = mixedMoment B node3047 node3047Labels := by rfl

def raw30234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw30234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 1, -3], ![2, -3, 1]]
def raw30234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw30234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30234 raw30234Labels = mixedMoment B node3026 node3026Labels := by
  calc
    mixedMoment B raw30234 raw30234Labels = mixedMoment B raw30234step0 raw30234step0Labels := by
      have hz : ∀ j, raw30234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30234step0 = (fun i j => raw30234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30234step0 raw30234; decide +kernel
      have hl : raw30234step0Labels = raw30234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30234 raw30234Labels permutation434 hz
    mixedMoment B raw30234step0 raw30234step0Labels = mixedMoment B raw30234step1 raw30234step1Labels := by
      have ha : raw30234step1 = (fun i j => raw30234step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30234step1 raw30234step0; decide +kernel
      have hl : raw30234step1Labels = raw30234step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30234step0 raw30234step0Labels permutation129 permutation4
    _ = mixedMoment B node3026 node3026Labels := by rfl

def raw30235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw30235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30235 raw30235Labels = mixedMoment B node3020 node3020Labels := by
  calc
    mixedMoment B raw30235 raw30235Labels = mixedMoment B raw30235step0 raw30235step0Labels := by
      have ha : raw30235step0 = (fun i j => raw30235 (permutation592 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30235step0 raw30235; decide +kernel
      have hl : raw30235step0Labels = raw30235Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30235 raw30235Labels permutation592 permutation4
    _ = mixedMoment B node3020 node3020Labels := by rfl

def raw30236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw30236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw30236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30236 raw30236Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw30236 raw30236Labels = mixedMoment B raw30236step0 raw30236step0Labels := by
      have hz : ∀ j, raw30236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30236step0 = (fun i j => raw30236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30236step0 raw30236; decide +kernel
      have hl : raw30236step0Labels = raw30236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30236 raw30236Labels permutation434 hz
    mixedMoment B raw30236step0 raw30236step0Labels = mixedMoment B raw30236step1 raw30236step1Labels := by
      have ha : raw30236step1 = (fun i j => raw30236step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30236step1 raw30236step0; decide +kernel
      have hl : raw30236step1Labels = raw30236step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30236step0 raw30236step0Labels permutation128 permutation4
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw30237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw30237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 1, -3], ![1, -2, 1]]
def raw30237step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30237step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30237 raw30237Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw30237 raw30237Labels = mixedMoment B raw30237step0 raw30237step0Labels := by
      have hz : ∀ j, raw30237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30237step0 = (fun i j => raw30237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30237step0 raw30237; decide +kernel
      have hl : raw30237step0Labels = raw30237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30237 raw30237Labels permutation434 hz
    mixedMoment B raw30237step0 raw30237step0Labels = mixedMoment B raw30237step1 raw30237step1Labels := by
      have ha : raw30237step1 = (fun i j => raw30237step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30237step1 raw30237step0; decide +kernel
      have hl : raw30237step1Labels = raw30237step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30237step0 raw30237step0Labels permutation127 permutation2
    mixedMoment B raw30237step1 raw30237step1Labels = mixedMoment B raw30237step2 raw30237step2Labels := by
      have ha : raw30237step2 = -raw30237step1 := by apply Matrix.ext; change ∀ i j, raw30237step2 i j = -(raw30237step1 i j); unfold raw30237step2 raw30237step1; decide +kernel
      have hl : raw30237step2Labels = raw30237step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw30238 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![3, -3], ![-1, 1]]
def raw30238Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30238step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![3, -3], ![-1, 1]]
def raw30238step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30238step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw30238step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30238step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw30238step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30238 raw30238Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw30238 raw30238Labels = mixedMoment B raw30238step0 raw30238step0Labels := by
      have hz : ∀ j, raw30238 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30238step0 = (fun i j => raw30238 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30238step0 raw30238; decide +kernel
      have hl : raw30238step0Labels = raw30238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30238 raw30238Labels permutation434 hz
    mixedMoment B raw30238step0 raw30238step0Labels = mixedMoment B raw30238step1 raw30238step1Labels := by
      have ha : raw30238step1 = (fun i j => raw30238step0 (permutation119 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30238step1 raw30238step0; decide +kernel
      have hl : raw30238step1Labels = raw30238step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30238step0 raw30238step0Labels permutation119 permutation0
    mixedMoment B raw30238step1 raw30238step1Labels = mixedMoment B raw30238step2 raw30238step2Labels := by
      have ha : raw30238step2 = -raw30238step1 := by apply Matrix.ext; change ∀ i j, raw30238step2 i j = -(raw30238step1 i j); unfold raw30238step2 raw30238step1; decide +kernel
      have hl : raw30238step2Labels = raw30238step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw30239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30239 raw30239Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw30239 raw30239Labels = mixedMoment B raw30239step0 raw30239step0Labels := by
      have hz : ∀ j, raw30239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30239step0 = (fun i j => raw30239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30239step0 raw30239; decide +kernel
      have hl : raw30239step0Labels = raw30239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30239 raw30239Labels permutation434 hz
    mixedMoment B raw30239step0 raw30239step0Labels = mixedMoment B raw30239step1 raw30239step1Labels := by
      have ha : raw30239step1 = (fun i j => raw30239step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30239step1 raw30239step0; decide +kernel
      have hl : raw30239step1Labels = raw30239step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30239step0 raw30239step0Labels permutation33 permutation2
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw30240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30240 raw30240Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw30240 raw30240Labels = mixedMoment B raw30240step0 raw30240step0Labels := by
      have hz : ∀ j, raw30240 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30240step0 = (fun i j => raw30240 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30240step0 raw30240; decide +kernel
      have hl : raw30240step0Labels = raw30240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30240 raw30240Labels permutation434 hz
    mixedMoment B raw30240step0 raw30240step0Labels = mixedMoment B raw30240step1 raw30240step1Labels := by
      have ha : raw30240step1 = (fun i j => raw30240step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30240step1 raw30240step0; decide +kernel
      have hl : raw30240step1Labels = raw30240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30240step0 raw30240step0Labels permutation127 permutation2
    mixedMoment B raw30240step1 raw30240step1Labels = mixedMoment B raw30240step2 raw30240step2Labels := by
      have ha : raw30240step2 = -raw30240step1 := by apply Matrix.ext; change ∀ i j, raw30240step2 i j = -(raw30240step1 i j); unfold raw30240step2 raw30240step1; decide +kernel
      have hl : raw30240step2Labels = raw30240step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw30241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30241 raw30241Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw30241 raw30241Labels = mixedMoment B raw30241step0 raw30241step0Labels := by
      have ha : raw30241step0 = (fun i j => raw30241 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30241step0 raw30241; decide +kernel
      have hl : raw30241step0Labels = raw30241Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30241 raw30241Labels permutation584 permutation2
    mixedMoment B raw30241step0 raw30241step0Labels = mixedMoment B raw30241step1 raw30241step1Labels := by
      have ha : raw30241step1 = -raw30241step0 := by apply Matrix.ext; change ∀ i j, raw30241step1 i j = -(raw30241step0 i j); unfold raw30241step1 raw30241step0; decide +kernel
      have hl : raw30241step1Labels = raw30241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw30242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30242 raw30242Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw30242 raw30242Labels = mixedMoment B raw30242step0 raw30242step0Labels := by
      have hz : ∀ j, raw30242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30242step0 = (fun i j => raw30242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30242step0 raw30242; decide +kernel
      have hl : raw30242step0Labels = raw30242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30242 raw30242Labels permutation434 hz
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw30243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30243 raw30243Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw30243 raw30243Labels = mixedMoment B raw30243step0 raw30243step0Labels := by
      have hz : ∀ j, raw30243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30243step0 = (fun i j => raw30243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30243step0 raw30243; decide +kernel
      have hl : raw30243step0Labels = raw30243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30243 raw30243Labels permutation434 hz
    mixedMoment B raw30243step0 raw30243step0Labels = mixedMoment B raw30243step1 raw30243step1Labels := by
      have ha : raw30243step1 = (fun i j => raw30243step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30243step1 raw30243step0; decide +kernel
      have hl : raw30243step1Labels = raw30243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30243step0 raw30243step0Labels permutation33 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw30244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30244 raw30244Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw30244 raw30244Labels = mixedMoment B raw30244step0 raw30244step0Labels := by
      have hz : ∀ j, raw30244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30244step0 = (fun i j => raw30244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30244step0 raw30244; decide +kernel
      have hl : raw30244step0Labels = raw30244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30244 raw30244Labels permutation434 hz
    mixedMoment B raw30244step0 raw30244step0Labels = mixedMoment B raw30244step1 raw30244step1Labels := by
      have ha : raw30244step1 = (fun i j => raw30244step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30244step1 raw30244step0; decide +kernel
      have hl : raw30244step1Labels = raw30244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30244step0 raw30244step0Labels permutation33 permutation2
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw30245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30245 raw30245Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw30245 raw30245Labels = mixedMoment B raw30245step0 raw30245step0Labels := by
      have hz : ∀ j, raw30245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30245step0 = (fun i j => raw30245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30245step0 raw30245; decide +kernel
      have hl : raw30245step0Labels = raw30245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30245 raw30245Labels permutation434 hz
    mixedMoment B raw30245step0 raw30245step0Labels = mixedMoment B raw30245step1 raw30245step1Labels := by
      have ha : raw30245step1 = (fun i j => raw30245step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30245step1 raw30245step0; decide +kernel
      have hl : raw30245step1Labels = raw30245step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30245step0 raw30245step0Labels permutation39 permutation2
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw30246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30246 raw30246Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw30246 raw30246Labels = mixedMoment B raw30246step0 raw30246step0Labels := by
      have ha : raw30246step0 = (fun i j => raw30246 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30246step0 raw30246; decide +kernel
      have hl : raw30246step0Labels = raw30246Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30246 raw30246Labels permutation201 permutation2
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw30247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30247 raw30247Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw30247 raw30247Labels = mixedMoment B raw30247step0 raw30247step0Labels := by
      have hz : ∀ j, raw30247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30247step0 = (fun i j => raw30247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30247step0 raw30247; decide +kernel
      have hl : raw30247step0Labels = raw30247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30247 raw30247Labels permutation434 hz
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw30248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30248 raw30248Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw30248 raw30248Labels = mixedMoment B raw30248step0 raw30248step0Labels := by
      have hz : ∀ j, raw30248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30248step0 = (fun i j => raw30248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30248step0 raw30248; decide +kernel
      have hl : raw30248step0Labels = raw30248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30248 raw30248Labels permutation434 hz
    mixedMoment B raw30248step0 raw30248step0Labels = mixedMoment B raw30248step1 raw30248step1Labels := by
      have ha : raw30248step1 = (fun i j => raw30248step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30248step1 raw30248step0; decide +kernel
      have hl : raw30248step1Labels = raw30248step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30248step0 raw30248step0Labels permutation33 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw30249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30249 raw30249Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw30249 raw30249Labels = mixedMoment B raw30249step0 raw30249step0Labels := by
      have hz : ∀ j, raw30249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30249step0 = (fun i j => raw30249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30249step0 raw30249; decide +kernel
      have hl : raw30249step0Labels = raw30249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30249 raw30249Labels permutation434 hz
    mixedMoment B raw30249step0 raw30249step0Labels = mixedMoment B raw30249step1 raw30249step1Labels := by
      have ha : raw30249step1 = (fun i j => raw30249step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30249step1 raw30249step0; decide +kernel
      have hl : raw30249step1Labels = raw30249step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30249step0 raw30249step0Labels permutation33 permutation2
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw30250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30250 raw30250Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw30250 raw30250Labels = mixedMoment B raw30250step0 raw30250step0Labels := by
      have hz : ∀ j, raw30250 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30250step0 = (fun i j => raw30250 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30250step0 raw30250; decide +kernel
      have hl : raw30250step0Labels = raw30250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30250 raw30250Labels permutation434 hz
    mixedMoment B raw30250step0 raw30250step0Labels = mixedMoment B raw30250step1 raw30250step1Labels := by
      have ha : raw30250step1 = (fun i j => raw30250step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30250step1 raw30250step0; decide +kernel
      have hl : raw30250step1Labels = raw30250step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30250step0 raw30250step0Labels permutation33 permutation2
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw30251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30251 raw30251Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw30251 raw30251Labels = mixedMoment B raw30251step0 raw30251step0Labels := by
      have ha : raw30251step0 = (fun i j => raw30251 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30251step0 raw30251; decide +kernel
      have hl : raw30251step0Labels = raw30251Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30251 raw30251Labels permutation159 permutation2
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw30252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30252 raw30252Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw30252 raw30252Labels = mixedMoment B raw30252step0 raw30252step0Labels := by
      have hz : ∀ j, raw30252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30252step0 = (fun i j => raw30252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30252step0 raw30252; decide +kernel
      have hl : raw30252step0Labels = raw30252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30252 raw30252Labels permutation434 hz
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw30253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30253 raw30253Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw30253 raw30253Labels = mixedMoment B raw30253step0 raw30253step0Labels := by
      have hz : ∀ j, raw30253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30253step0 = (fun i j => raw30253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30253step0 raw30253; decide +kernel
      have hl : raw30253step0Labels = raw30253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30253 raw30253Labels permutation434 hz
    mixedMoment B raw30253step0 raw30253step0Labels = mixedMoment B raw30253step1 raw30253step1Labels := by
      have ha : raw30253step1 = (fun i j => raw30253step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30253step1 raw30253step0; decide +kernel
      have hl : raw30253step1Labels = raw30253step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30253step0 raw30253step0Labels permutation36 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw30254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30254 raw30254Labels = mixedMoment B node4529 node4529Labels := by
  calc
    mixedMoment B raw30254 raw30254Labels = mixedMoment B raw30254step0 raw30254step0Labels := by
      have ha : raw30254step0 = (fun i j => raw30254 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30254step0 raw30254; decide +kernel
      have hl : raw30254step0Labels = raw30254Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30254 raw30254Labels permutation153 permutation2
    _ = mixedMoment B node4529 node4529Labels := by rfl

def raw30255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30255 raw30255Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw30255 raw30255Labels = mixedMoment B raw30255step0 raw30255step0Labels := by
      have ha : raw30255step0 = (fun i j => raw30255 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30255step0 raw30255; decide +kernel
      have hl : raw30255step0Labels = raw30255Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30255 raw30255Labels permutation153 permutation2
    _ = mixedMoment B node4931 node4931Labels := by rfl

def raw30256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30256 raw30256Labels = mixedMoment B node5042 node5042Labels := by
  calc
    mixedMoment B raw30256 raw30256Labels = mixedMoment B raw30256step0 raw30256step0Labels := by
      have ha : raw30256step0 = (fun i j => raw30256 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30256step0 raw30256; decide +kernel
      have hl : raw30256step0Labels = raw30256Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30256 raw30256Labels permutation153 permutation2
    _ = mixedMoment B node5042 node5042Labels := by rfl

def raw30257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30257 raw30257Labels = mixedMoment B node5074 node5074Labels := by
  calc
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw30258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30258 raw30258Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw30258 raw30258Labels = mixedMoment B raw30258step0 raw30258step0Labels := by
      have ha : raw30258step0 = (fun i j => raw30258 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30258step0 raw30258; decide +kernel
      have hl : raw30258step0Labels = raw30258Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30258 raw30258Labels permutation153 permutation2
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw30259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30259 raw30259Labels = mixedMoment B node4534 node4534Labels := by
  calc
    mixedMoment B raw30259 raw30259Labels = mixedMoment B raw30259step0 raw30259step0Labels := by
      have hz : ∀ j, raw30259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30259step0 = (fun i j => raw30259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30259step0 raw30259; decide +kernel
      have hl : raw30259step0Labels = raw30259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30259 raw30259Labels permutation434 hz
    mixedMoment B raw30259step0 raw30259step0Labels = mixedMoment B raw30259step1 raw30259step1Labels := by
      have ha : raw30259step1 = (fun i j => raw30259step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30259step1 raw30259step0; decide +kernel
      have hl : raw30259step1Labels = raw30259step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30259step0 raw30259step0Labels permutation33 permutation2
    _ = mixedMoment B node4534 node4534Labels := by rfl

def raw30260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30260 raw30260Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw30260 raw30260Labels = mixedMoment B raw30260step0 raw30260step0Labels := by
      have hz : ∀ j, raw30260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30260step0 = (fun i j => raw30260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30260step0 raw30260; decide +kernel
      have hl : raw30260step0Labels = raw30260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30260 raw30260Labels permutation434 hz
    mixedMoment B raw30260step0 raw30260step0Labels = mixedMoment B raw30260step1 raw30260step1Labels := by
      have ha : raw30260step1 = (fun i j => raw30260step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30260step1 raw30260step0; decide +kernel
      have hl : raw30260step1Labels = raw30260step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30260step0 raw30260step0Labels permutation33 permutation2
    _ = mixedMoment B node4934 node4934Labels := by rfl

def raw30261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30261 raw30261Labels = mixedMoment B node4965 node4965Labels := by
  calc
    mixedMoment B raw30261 raw30261Labels = mixedMoment B raw30261step0 raw30261step0Labels := by
      have hz : ∀ j, raw30261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30261step0 = (fun i j => raw30261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30261step0 raw30261; decide +kernel
      have hl : raw30261step0Labels = raw30261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30261 raw30261Labels permutation434 hz
    mixedMoment B raw30261step0 raw30261step0Labels = mixedMoment B raw30261step1 raw30261step1Labels := by
      have ha : raw30261step1 = (fun i j => raw30261step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30261step1 raw30261step0; decide +kernel
      have hl : raw30261step1Labels = raw30261step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30261step0 raw30261step0Labels permutation127 permutation2
    mixedMoment B raw30261step1 raw30261step1Labels = mixedMoment B raw30261step2 raw30261step2Labels := by
      have ha : raw30261step2 = -raw30261step1 := by apply Matrix.ext; change ∀ i j, raw30261step2 i j = -(raw30261step1 i j); unfold raw30261step2 raw30261step1; decide +kernel
      have hl : raw30261step2Labels = raw30261step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4965 node4965Labels := by rfl

def raw30262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30262 raw30262Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw30262 raw30262Labels = mixedMoment B raw30262step0 raw30262step0Labels := by
      have ha : raw30262step0 = (fun i j => raw30262 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30262step0 raw30262; decide +kernel
      have hl : raw30262step0Labels = raw30262Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30262 raw30262Labels permutation584 permutation2
    mixedMoment B raw30262step0 raw30262step0Labels = mixedMoment B raw30262step1 raw30262step1Labels := by
      have ha : raw30262step1 = -raw30262step0 := by apply Matrix.ext; change ∀ i j, raw30262step1 i j = -(raw30262step0 i j); unfold raw30262step1 raw30262step0; decide +kernel
      have hl : raw30262step1Labels = raw30262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4954 node4954Labels := by rfl

def raw30263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30263 raw30263Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw30263 raw30263Labels = mixedMoment B raw30263step0 raw30263step0Labels := by
      have hz : ∀ j, raw30263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30263step0 = (fun i j => raw30263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30263step0 raw30263; decide +kernel
      have hl : raw30263step0Labels = raw30263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30263 raw30263Labels permutation434 hz
    mixedMoment B raw30263step0 raw30263step0Labels = mixedMoment B raw30263step1 raw30263step1Labels := by
      have ha : raw30263step1 = (fun i j => raw30263step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30263step1 raw30263step0; decide +kernel
      have hl : raw30263step1Labels = raw30263step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30263step0 raw30263step0Labels permutation33 permutation2
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw30264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30264 raw30264Labels = mixedMoment B node4536 node4536Labels := by
  calc
    mixedMoment B raw30264 raw30264Labels = mixedMoment B raw30264step0 raw30264step0Labels := by
      have hz : ∀ j, raw30264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30264step0 = (fun i j => raw30264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30264step0 raw30264; decide +kernel
      have hl : raw30264step0Labels = raw30264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30264 raw30264Labels permutation434 hz
    _ = mixedMoment B node4536 node4536Labels := by rfl

def raw30265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw30265step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30265step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30265step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30265step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30265 raw30265Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw30265 raw30265Labels = mixedMoment B raw30265step0 raw30265step0Labels := by
      have hz : ∀ j, raw30265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30265step0 = (fun i j => raw30265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30265step0 raw30265; decide +kernel
      have hl : raw30265step0Labels = raw30265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30265 raw30265Labels permutation434 hz
    mixedMoment B raw30265step0 raw30265step0Labels = mixedMoment B raw30265step1 raw30265step1Labels := by
      have ha : raw30265step1 = (fun i j => raw30265step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30265step1 raw30265step0; decide +kernel
      have hl : raw30265step1Labels = raw30265step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30265step0 raw30265step0Labels permutation151 permutation3
    mixedMoment B raw30265step1 raw30265step1Labels = mixedMoment B raw30265step2 raw30265step2Labels := by
      have ha : raw30265step2 = -raw30265step1 := by apply Matrix.ext; change ∀ i j, raw30265step2 i j = -(raw30265step1 i j); unfold raw30265step2 raw30265step1; decide +kernel
      have hl : raw30265step2Labels = raw30265step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30265step2 raw30265step2Labels = mixedMoment B raw30265step3 raw30265step3Labels := by
      have ha : raw30265step3 = raw30265step2 := by apply Matrix.ext; unfold raw30265step3 raw30265step2; decide +kernel
      have hl : raw30265step2Labels = labelEmbedding6 ∘ raw30265step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30265step2 raw30265step2Labels raw30265step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4670 node4670Labels := by rfl

def raw30266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw30266step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30266step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30266step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30266 raw30266Labels = mixedMoment B node4682 node4682Labels := by
  calc
    mixedMoment B raw30266 raw30266Labels = mixedMoment B raw30266step0 raw30266step0Labels := by
      have hz : ∀ j, raw30266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30266step0 = (fun i j => raw30266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30266step0 raw30266; decide +kernel
      have hl : raw30266step0Labels = raw30266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30266 raw30266Labels permutation434 hz
    mixedMoment B raw30266step0 raw30266step0Labels = mixedMoment B raw30266step1 raw30266step1Labels := by
      have ha : raw30266step1 = (fun i j => raw30266step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30266step1 raw30266step0; decide +kernel
      have hl : raw30266step1Labels = raw30266step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30266step0 raw30266step0Labels permutation149 permutation3
    mixedMoment B raw30266step1 raw30266step1Labels = mixedMoment B raw30266step2 raw30266step2Labels := by
      have ha : raw30266step2 = -raw30266step1 := by apply Matrix.ext; change ∀ i j, raw30266step2 i j = -(raw30266step1 i j); unfold raw30266step2 raw30266step1; decide +kernel
      have hl : raw30266step2Labels = raw30266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30266step2 raw30266step2Labels = mixedMoment B raw30266step3 raw30266step3Labels := by
      have ha : raw30266step3 = raw30266step2 := by apply Matrix.ext; unfold raw30266step3 raw30266step2; decide +kernel
      have hl : raw30266step2Labels = labelEmbedding6 ∘ raw30266step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30266step2 raw30266step2Labels raw30266step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4682 node4682Labels := by rfl

def raw30267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30267step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30267step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30267step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30267 raw30267Labels = mixedMoment B node4664 node4664Labels := by
  calc
    mixedMoment B raw30267 raw30267Labels = mixedMoment B raw30267step0 raw30267step0Labels := by
      have ha : raw30267step0 = (fun i j => raw30267 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30267step0 raw30267; decide +kernel
      have hl : raw30267step0Labels = raw30267Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30267 raw30267Labels permutation680 permutation3
    mixedMoment B raw30267step0 raw30267step0Labels = mixedMoment B raw30267step1 raw30267step1Labels := by
      have ha : raw30267step1 = -raw30267step0 := by apply Matrix.ext; change ∀ i j, raw30267step1 i j = -(raw30267step0 i j); unfold raw30267step1 raw30267step0; decide +kernel
      have hl : raw30267step1Labels = raw30267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30267step1 raw30267step1Labels = mixedMoment B raw30267step2 raw30267step2Labels := by
      have ha : raw30267step2 = raw30267step1 := by apply Matrix.ext; unfold raw30267step2 raw30267step1; decide +kernel
      have hl : raw30267step1Labels = labelEmbedding6 ∘ raw30267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30267step1 raw30267step1Labels raw30267step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4664 node4664Labels := by rfl

def raw30268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw30268step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw30268step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw30268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30268 raw30268Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw30268 raw30268Labels = mixedMoment B raw30268step0 raw30268step0Labels := by
      have hz : ∀ j, raw30268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30268step0 = (fun i j => raw30268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30268step0 raw30268; decide +kernel
      have hl : raw30268step0Labels = raw30268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30268 raw30268Labels permutation434 hz
    mixedMoment B raw30268step0 raw30268step0Labels = mixedMoment B raw30268step1 raw30268step1Labels := by
      have ha : raw30268step1 = (fun i j => raw30268step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30268step1 raw30268step0; decide +kernel
      have hl : raw30268step1Labels = raw30268step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30268step0 raw30268step0Labels permutation151 permutation3
    mixedMoment B raw30268step1 raw30268step1Labels = mixedMoment B raw30268step2 raw30268step2Labels := by
      have ha : raw30268step2 = -raw30268step1 := by apply Matrix.ext; change ∀ i j, raw30268step2 i j = -(raw30268step1 i j); unfold raw30268step2 raw30268step1; decide +kernel
      have hl : raw30268step2Labels = raw30268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30268step2 raw30268step2Labels = mixedMoment B raw30268step3 raw30268step3Labels := by
      have ha : raw30268step3 = raw30268step2 := by apply Matrix.ext; unfold raw30268step3 raw30268step2; decide +kernel
      have hl : raw30268step2Labels = labelEmbedding6 ∘ raw30268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30268step2 raw30268step2Labels raw30268step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw30269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30269step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30269step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30269step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30269step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30269 raw30269Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw30269 raw30269Labels = mixedMoment B raw30269step0 raw30269step0Labels := by
      have hz : ∀ j, raw30269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30269step0 = (fun i j => raw30269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30269step0 raw30269; decide +kernel
      have hl : raw30269step0Labels = raw30269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30269 raw30269Labels permutation434 hz
    mixedMoment B raw30269step0 raw30269step0Labels = mixedMoment B raw30269step1 raw30269step1Labels := by
      have ha : raw30269step1 = (fun i j => raw30269step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30269step1 raw30269step0; decide +kernel
      have hl : raw30269step1Labels = raw30269step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30269step0 raw30269step0Labels permutation36 permutation7
    mixedMoment B raw30269step1 raw30269step1Labels = mixedMoment B raw30269step2 raw30269step2Labels := by
      have ha : raw30269step2 = -raw30269step1 := by apply Matrix.ext; change ∀ i j, raw30269step2 i j = -(raw30269step1 i j); unfold raw30269step2 raw30269step1; decide +kernel
      have hl : raw30269step2Labels = raw30269step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30269step2 raw30269step2Labels = mixedMoment B raw30269step3 raw30269step3Labels := by
      have ha : raw30269step3 = raw30269step2 := by apply Matrix.ext; unfold raw30269step3 raw30269step2; decide +kernel
      have hl : raw30269step2Labels = labelEmbedding1 ∘ raw30269step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30269step2 raw30269step2Labels raw30269step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw30270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30270step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30270step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30270step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30270step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30270step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30270 raw30270Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw30270 raw30270Labels = mixedMoment B raw30270step0 raw30270step0Labels := by
      have hz : ∀ j, raw30270 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30270step0 = (fun i j => raw30270 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30270step0 raw30270; decide +kernel
      have hl : raw30270step0Labels = raw30270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30270 raw30270Labels permutation434 hz
    mixedMoment B raw30270step0 raw30270step0Labels = mixedMoment B raw30270step1 raw30270step1Labels := by
      have ha : raw30270step1 = (fun i j => raw30270step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30270step1 raw30270step0; decide +kernel
      have hl : raw30270step1Labels = raw30270step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30270step0 raw30270step0Labels permutation36 permutation7
    mixedMoment B raw30270step1 raw30270step1Labels = mixedMoment B raw30270step2 raw30270step2Labels := by
      have ha : raw30270step2 = -raw30270step1 := by apply Matrix.ext; change ∀ i j, raw30270step2 i j = -(raw30270step1 i j); unfold raw30270step2 raw30270step1; decide +kernel
      have hl : raw30270step2Labels = raw30270step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30270step2 raw30270step2Labels = mixedMoment B raw30270step3 raw30270step3Labels := by
      have ha : raw30270step3 = raw30270step2 := by apply Matrix.ext; unfold raw30270step3 raw30270step2; decide +kernel
      have hl : raw30270step2Labels = labelEmbedding1 ∘ raw30270step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30270step2 raw30270step2Labels raw30270step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw30271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30271 raw30271Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw30271 raw30271Labels = mixedMoment B raw30271step0 raw30271step0Labels := by
      have ha : raw30271step0 = (fun i j => raw30271 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30271step0 raw30271; decide +kernel
      have hl : raw30271step0Labels = raw30271Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30271 raw30271Labels permutation162 permutation7
    mixedMoment B raw30271step0 raw30271step0Labels = mixedMoment B raw30271step1 raw30271step1Labels := by
      have ha : raw30271step1 = -raw30271step0 := by apply Matrix.ext; change ∀ i j, raw30271step1 i j = -(raw30271step0 i j); unfold raw30271step1 raw30271step0; decide +kernel
      have hl : raw30271step1Labels = raw30271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30271step1 raw30271step1Labels = mixedMoment B raw30271step2 raw30271step2Labels := by
      have ha : raw30271step2 = raw30271step1 := by apply Matrix.ext; unfold raw30271step2 raw30271step1; decide +kernel
      have hl : raw30271step1Labels = labelEmbedding1 ∘ raw30271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30271step1 raw30271step1Labels raw30271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw30272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30272step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw30272step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30272step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30272 raw30272Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw30272 raw30272Labels = mixedMoment B raw30272step0 raw30272step0Labels := by
      have hz : ∀ j, raw30272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30272step0 = (fun i j => raw30272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30272step0 raw30272; decide +kernel
      have hl : raw30272step0Labels = raw30272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30272 raw30272Labels permutation434 hz
    mixedMoment B raw30272step0 raw30272step0Labels = mixedMoment B raw30272step1 raw30272step1Labels := by
      have ha : raw30272step1 = (fun i j => raw30272step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30272step1 raw30272step0; decide +kernel
      have hl : raw30272step1Labels = raw30272step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30272step0 raw30272step0Labels permutation36 permutation7
    mixedMoment B raw30272step1 raw30272step1Labels = mixedMoment B raw30272step2 raw30272step2Labels := by
      have ha : raw30272step2 = -raw30272step1 := by apply Matrix.ext; change ∀ i j, raw30272step2 i j = -(raw30272step1 i j); unfold raw30272step2 raw30272step1; decide +kernel
      have hl : raw30272step2Labels = raw30272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30272step2 raw30272step2Labels = mixedMoment B raw30272step3 raw30272step3Labels := by
      have ha : raw30272step3 = raw30272step2 := by apply Matrix.ext; unfold raw30272step3 raw30272step2; decide +kernel
      have hl : raw30272step2Labels = labelEmbedding1 ∘ raw30272step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30272step2 raw30272step2Labels raw30272step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw30273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30273step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30273 raw30273Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw30273 raw30273Labels = mixedMoment B raw30273step0 raw30273step0Labels := by
      have hz : ∀ j, raw30273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30273step0 = (fun i j => raw30273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30273step0 raw30273; decide +kernel
      have hl : raw30273step0Labels = raw30273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30273 raw30273Labels permutation434 hz
    mixedMoment B raw30273step0 raw30273step0Labels = mixedMoment B raw30273step1 raw30273step1Labels := by
      have ha : raw30273step1 = (fun i j => raw30273step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30273step1 raw30273step0; decide +kernel
      have hl : raw30273step1Labels = raw30273step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30273step0 raw30273step0Labels permutation36 permutation7
    mixedMoment B raw30273step1 raw30273step1Labels = mixedMoment B raw30273step2 raw30273step2Labels := by
      have ha : raw30273step2 = -raw30273step1 := by apply Matrix.ext; change ∀ i j, raw30273step2 i j = -(raw30273step1 i j); unfold raw30273step2 raw30273step1; decide +kernel
      have hl : raw30273step2Labels = raw30273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30273step2 raw30273step2Labels = mixedMoment B raw30273step3 raw30273step3Labels := by
      have ha : raw30273step3 = raw30273step2 := by apply Matrix.ext; unfold raw30273step3 raw30273step2; decide +kernel
      have hl : raw30273step2Labels = labelEmbedding1 ∘ raw30273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30273step2 raw30273step2Labels raw30273step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw30274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30274step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30274step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30274step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30274step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30274step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30274 raw30274Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw30274 raw30274Labels = mixedMoment B raw30274step0 raw30274step0Labels := by
      have hz : ∀ j, raw30274 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30274step0 = (fun i j => raw30274 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30274step0 raw30274; decide +kernel
      have hl : raw30274step0Labels = raw30274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30274 raw30274Labels permutation434 hz
    mixedMoment B raw30274step0 raw30274step0Labels = mixedMoment B raw30274step1 raw30274step1Labels := by
      have ha : raw30274step1 = (fun i j => raw30274step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30274step1 raw30274step0; decide +kernel
      have hl : raw30274step1Labels = raw30274step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30274step0 raw30274step0Labels permutation40 permutation5
    mixedMoment B raw30274step1 raw30274step1Labels = mixedMoment B raw30274step2 raw30274step2Labels := by
      have ha : raw30274step2 = -raw30274step1 := by apply Matrix.ext; change ∀ i j, raw30274step2 i j = -(raw30274step1 i j); unfold raw30274step2 raw30274step1; decide +kernel
      have hl : raw30274step2Labels = raw30274step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30274step2 raw30274step2Labels = mixedMoment B raw30274step3 raw30274step3Labels := by
      have ha : raw30274step3 = raw30274step2 := by apply Matrix.ext; unfold raw30274step3 raw30274step2; decide +kernel
      have hl : raw30274step2Labels = labelEmbedding1 ∘ raw30274step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30274step2 raw30274step2Labels raw30274step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

def raw30275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30275Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30275step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30275step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30275step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30275step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30275step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30275 raw30275Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw30275 raw30275Labels = mixedMoment B raw30275step0 raw30275step0Labels := by
      have hz : ∀ j, raw30275 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30275step0 = (fun i j => raw30275 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30275step0 raw30275; decide +kernel
      have hl : raw30275step0Labels = raw30275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30275 raw30275Labels permutation434 hz
    mixedMoment B raw30275step0 raw30275step0Labels = mixedMoment B raw30275step1 raw30275step1Labels := by
      have ha : raw30275step1 = (fun i j => raw30275step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30275step1 raw30275step0; decide +kernel
      have hl : raw30275step1Labels = raw30275step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30275step0 raw30275step0Labels permutation36 permutation7
    mixedMoment B raw30275step1 raw30275step1Labels = mixedMoment B raw30275step2 raw30275step2Labels := by
      have ha : raw30275step2 = -raw30275step1 := by apply Matrix.ext; change ∀ i j, raw30275step2 i j = -(raw30275step1 i j); unfold raw30275step2 raw30275step1; decide +kernel
      have hl : raw30275step2Labels = raw30275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30275step2 raw30275step2Labels = mixedMoment B raw30275step3 raw30275step3Labels := by
      have ha : raw30275step3 = raw30275step2 := by apply Matrix.ext; unfold raw30275step3 raw30275step2; decide +kernel
      have hl : raw30275step2Labels = labelEmbedding1 ∘ raw30275step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30275step2 raw30275step2Labels raw30275step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw30276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30276Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30276step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30276 raw30276Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw30276 raw30276Labels = mixedMoment B raw30276step0 raw30276step0Labels := by
      have ha : raw30276step0 = (fun i j => raw30276 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30276step0 raw30276; decide +kernel
      have hl : raw30276step0Labels = raw30276Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30276 raw30276Labels permutation162 permutation7
    mixedMoment B raw30276step0 raw30276step0Labels = mixedMoment B raw30276step1 raw30276step1Labels := by
      have ha : raw30276step1 = -raw30276step0 := by apply Matrix.ext; change ∀ i j, raw30276step1 i j = -(raw30276step0 i j); unfold raw30276step1 raw30276step0; decide +kernel
      have hl : raw30276step1Labels = raw30276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30276step1 raw30276step1Labels = mixedMoment B raw30276step2 raw30276step2Labels := by
      have ha : raw30276step2 = raw30276step1 := by apply Matrix.ext; unfold raw30276step2 raw30276step1; decide +kernel
      have hl : raw30276step1Labels = labelEmbedding1 ∘ raw30276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30276step1 raw30276step1Labels raw30276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw30277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30277Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30277step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw30277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30277step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30277step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30277step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30277 raw30277Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw30277 raw30277Labels = mixedMoment B raw30277step0 raw30277step0Labels := by
      have hz : ∀ j, raw30277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30277step0 = (fun i j => raw30277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30277step0 raw30277; decide +kernel
      have hl : raw30277step0Labels = raw30277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30277 raw30277Labels permutation434 hz
    mixedMoment B raw30277step0 raw30277step0Labels = mixedMoment B raw30277step1 raw30277step1Labels := by
      have ha : raw30277step1 = (fun i j => raw30277step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30277step1 raw30277step0; decide +kernel
      have hl : raw30277step1Labels = raw30277step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30277step0 raw30277step0Labels permutation36 permutation7
    mixedMoment B raw30277step1 raw30277step1Labels = mixedMoment B raw30277step2 raw30277step2Labels := by
      have ha : raw30277step2 = -raw30277step1 := by apply Matrix.ext; change ∀ i j, raw30277step2 i j = -(raw30277step1 i j); unfold raw30277step2 raw30277step1; decide +kernel
      have hl : raw30277step2Labels = raw30277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30277step2 raw30277step2Labels = mixedMoment B raw30277step3 raw30277step3Labels := by
      have ha : raw30277step3 = raw30277step2 := by apply Matrix.ext; unfold raw30277step3 raw30277step2; decide +kernel
      have hl : raw30277step2Labels = labelEmbedding1 ∘ raw30277step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30277step2 raw30277step2Labels raw30277step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw30278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30278step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30278step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30278step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30278step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30278 raw30278Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw30278 raw30278Labels = mixedMoment B raw30278step0 raw30278step0Labels := by
      have hz : ∀ j, raw30278 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30278step0 = (fun i j => raw30278 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30278step0 raw30278; decide +kernel
      have hl : raw30278step0Labels = raw30278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30278 raw30278Labels permutation434 hz
    mixedMoment B raw30278step0 raw30278step0Labels = mixedMoment B raw30278step1 raw30278step1Labels := by
      have ha : raw30278step1 = (fun i j => raw30278step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30278step1 raw30278step0; decide +kernel
      have hl : raw30278step1Labels = raw30278step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30278step0 raw30278step0Labels permutation36 permutation7
    mixedMoment B raw30278step1 raw30278step1Labels = mixedMoment B raw30278step2 raw30278step2Labels := by
      have ha : raw30278step2 = -raw30278step1 := by apply Matrix.ext; change ∀ i j, raw30278step2 i j = -(raw30278step1 i j); unfold raw30278step2 raw30278step1; decide +kernel
      have hl : raw30278step2Labels = raw30278step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30278step2 raw30278step2Labels = mixedMoment B raw30278step3 raw30278step3Labels := by
      have ha : raw30278step3 = raw30278step2 := by apply Matrix.ext; unfold raw30278step3 raw30278step2; decide +kernel
      have hl : raw30278step2Labels = labelEmbedding1 ∘ raw30278step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30278step2 raw30278step2Labels raw30278step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw30279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30279step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw30279step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30279step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30279step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30279step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30279 raw30279Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw30279 raw30279Labels = mixedMoment B raw30279step0 raw30279step0Labels := by
      have hz : ∀ j, raw30279 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30279step0 = (fun i j => raw30279 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30279step0 raw30279; decide +kernel
      have hl : raw30279step0Labels = raw30279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30279 raw30279Labels permutation434 hz
    mixedMoment B raw30279step0 raw30279step0Labels = mixedMoment B raw30279step1 raw30279step1Labels := by
      have ha : raw30279step1 = (fun i j => raw30279step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30279step1 raw30279step0; decide +kernel
      have hl : raw30279step1Labels = raw30279step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30279step0 raw30279step0Labels permutation36 permutation7
    mixedMoment B raw30279step1 raw30279step1Labels = mixedMoment B raw30279step2 raw30279step2Labels := by
      have ha : raw30279step2 = -raw30279step1 := by apply Matrix.ext; change ∀ i j, raw30279step2 i j = -(raw30279step1 i j); unfold raw30279step2 raw30279step1; decide +kernel
      have hl : raw30279step2Labels = raw30279step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30279step2 raw30279step2Labels = mixedMoment B raw30279step3 raw30279step3Labels := by
      have ha : raw30279step3 = raw30279step2 := by apply Matrix.ext; unfold raw30279step3 raw30279step2; decide +kernel
      have hl : raw30279step2Labels = labelEmbedding1 ∘ raw30279step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30279step2 raw30279step2Labels raw30279step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3270 node3270Labels := by rfl

def raw30280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30280step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw30280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30280step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30280step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30280step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30280 raw30280Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw30280 raw30280Labels = mixedMoment B raw30280step0 raw30280step0Labels := by
      have hz : ∀ j, raw30280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30280step0 = (fun i j => raw30280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30280step0 raw30280; decide +kernel
      have hl : raw30280step0Labels = raw30280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30280 raw30280Labels permutation434 hz
    mixedMoment B raw30280step0 raw30280step0Labels = mixedMoment B raw30280step1 raw30280step1Labels := by
      have ha : raw30280step1 = (fun i j => raw30280step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30280step1 raw30280step0; decide +kernel
      have hl : raw30280step1Labels = raw30280step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30280step0 raw30280step0Labels permutation36 permutation7
    mixedMoment B raw30280step1 raw30280step1Labels = mixedMoment B raw30280step2 raw30280step2Labels := by
      have ha : raw30280step2 = -raw30280step1 := by apply Matrix.ext; change ∀ i j, raw30280step2 i j = -(raw30280step1 i j); unfold raw30280step2 raw30280step1; decide +kernel
      have hl : raw30280step2Labels = raw30280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30280step2 raw30280step2Labels = mixedMoment B raw30280step3 raw30280step3Labels := by
      have ha : raw30280step3 = raw30280step2 := by apply Matrix.ext; unfold raw30280step3 raw30280step2; decide +kernel
      have hl : raw30280step2Labels = labelEmbedding1 ∘ raw30280step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30280step2 raw30280step2Labels raw30280step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

def raw30281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw30281step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30281step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30281step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30281 raw30281Labels = mixedMoment B node3453 node3453Labels := by
  calc
    mixedMoment B raw30281 raw30281Labels = mixedMoment B raw30281step0 raw30281step0Labels := by
      have ha : raw30281step0 = (fun i j => raw30281 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30281step0 raw30281; decide +kernel
      have hl : raw30281step0Labels = raw30281Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30281 raw30281Labels permutation162 permutation7
    mixedMoment B raw30281step0 raw30281step0Labels = mixedMoment B raw30281step1 raw30281step1Labels := by
      have ha : raw30281step1 = -raw30281step0 := by apply Matrix.ext; change ∀ i j, raw30281step1 i j = -(raw30281step0 i j); unfold raw30281step1 raw30281step0; decide +kernel
      have hl : raw30281step1Labels = raw30281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30281step1 raw30281step1Labels = mixedMoment B raw30281step2 raw30281step2Labels := by
      have ha : raw30281step2 = raw30281step1 := by apply Matrix.ext; unfold raw30281step2 raw30281step1; decide +kernel
      have hl : raw30281step1Labels = labelEmbedding1 ∘ raw30281step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30281step1 raw30281step1Labels raw30281step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3453 node3453Labels := by rfl

def raw30282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30282step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw30282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30282step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30282step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30282 raw30282Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw30282 raw30282Labels = mixedMoment B raw30282step0 raw30282step0Labels := by
      have hz : ∀ j, raw30282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30282step0 = (fun i j => raw30282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30282step0 raw30282; decide +kernel
      have hl : raw30282step0Labels = raw30282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30282 raw30282Labels permutation434 hz
    mixedMoment B raw30282step0 raw30282step0Labels = mixedMoment B raw30282step1 raw30282step1Labels := by
      have ha : raw30282step1 = (fun i j => raw30282step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30282step1 raw30282step0; decide +kernel
      have hl : raw30282step1Labels = raw30282step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30282step0 raw30282step0Labels permutation36 permutation7
    mixedMoment B raw30282step1 raw30282step1Labels = mixedMoment B raw30282step2 raw30282step2Labels := by
      have ha : raw30282step2 = -raw30282step1 := by apply Matrix.ext; change ∀ i j, raw30282step2 i j = -(raw30282step1 i j); unfold raw30282step2 raw30282step1; decide +kernel
      have hl : raw30282step2Labels = raw30282step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30282step2 raw30282step2Labels = mixedMoment B raw30282step3 raw30282step3Labels := by
      have ha : raw30282step3 = raw30282step2 := by apply Matrix.ext; unfold raw30282step3 raw30282step2; decide +kernel
      have hl : raw30282step2Labels = labelEmbedding1 ∘ raw30282step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30282step2 raw30282step2Labels raw30282step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

def raw30283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30283step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30283step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30283step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30283step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30283 raw30283Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw30283 raw30283Labels = mixedMoment B raw30283step0 raw30283step0Labels := by
      have hz : ∀ j, raw30283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30283step0 = (fun i j => raw30283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30283step0 raw30283; decide +kernel
      have hl : raw30283step0Labels = raw30283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30283 raw30283Labels permutation434 hz
    mixedMoment B raw30283step0 raw30283step0Labels = mixedMoment B raw30283step1 raw30283step1Labels := by
      have ha : raw30283step1 = (fun i j => raw30283step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30283step1 raw30283step0; decide +kernel
      have hl : raw30283step1Labels = raw30283step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30283step0 raw30283step0Labels permutation36 permutation7
    mixedMoment B raw30283step1 raw30283step1Labels = mixedMoment B raw30283step2 raw30283step2Labels := by
      have ha : raw30283step2 = -raw30283step1 := by apply Matrix.ext; change ∀ i j, raw30283step2 i j = -(raw30283step1 i j); unfold raw30283step2 raw30283step1; decide +kernel
      have hl : raw30283step2Labels = raw30283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30283step2 raw30283step2Labels = mixedMoment B raw30283step3 raw30283step3Labels := by
      have ha : raw30283step3 = raw30283step2 := by apply Matrix.ext; unfold raw30283step3 raw30283step2; decide +kernel
      have hl : raw30283step2Labels = labelEmbedding1 ∘ raw30283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30283step2 raw30283step2Labels raw30283step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

def raw30284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30284step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30284 raw30284Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw30284 raw30284Labels = mixedMoment B raw30284step0 raw30284step0Labels := by
      have ha : raw30284step0 = (fun i j => raw30284 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30284step0 raw30284; decide +kernel
      have hl : raw30284step0Labels = raw30284Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30284 raw30284Labels permutation162 permutation7
    mixedMoment B raw30284step0 raw30284step0Labels = mixedMoment B raw30284step1 raw30284step1Labels := by
      have ha : raw30284step1 = -raw30284step0 := by apply Matrix.ext; change ∀ i j, raw30284step1 i j = -(raw30284step0 i j); unfold raw30284step1 raw30284step0; decide +kernel
      have hl : raw30284step1Labels = raw30284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30284step1 raw30284step1Labels = mixedMoment B raw30284step2 raw30284step2Labels := by
      have ha : raw30284step2 = raw30284step1 := by apply Matrix.ext; unfold raw30284step2 raw30284step1; decide +kernel
      have hl : raw30284step1Labels = labelEmbedding1 ∘ raw30284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30284step1 raw30284step1Labels raw30284step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

def raw30285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30285step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30285 raw30285Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw30285 raw30285Labels = mixedMoment B raw30285step0 raw30285step0Labels := by
      have ha : raw30285step0 = (fun i j => raw30285 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30285step0 raw30285; decide +kernel
      have hl : raw30285step0Labels = raw30285Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30285 raw30285Labels permutation162 permutation7
    mixedMoment B raw30285step0 raw30285step0Labels = mixedMoment B raw30285step1 raw30285step1Labels := by
      have ha : raw30285step1 = -raw30285step0 := by apply Matrix.ext; change ∀ i j, raw30285step1 i j = -(raw30285step0 i j); unfold raw30285step1 raw30285step0; decide +kernel
      have hl : raw30285step1Labels = raw30285step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30285step1 raw30285step1Labels = mixedMoment B raw30285step2 raw30285step2Labels := by
      have ha : raw30285step2 = raw30285step1 := by apply Matrix.ext; unfold raw30285step2 raw30285step1; decide +kernel
      have hl : raw30285step1Labels = labelEmbedding1 ∘ raw30285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30285step1 raw30285step1Labels raw30285step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw30286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30286 raw30286Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw30286 raw30286Labels = mixedMoment B raw30286step0 raw30286step0Labels := by
      have ha : raw30286step0 = (fun i j => raw30286 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30286step0 raw30286; decide +kernel
      have hl : raw30286step0Labels = raw30286Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30286 raw30286Labels permutation162 permutation7
    mixedMoment B raw30286step0 raw30286step0Labels = mixedMoment B raw30286step1 raw30286step1Labels := by
      have ha : raw30286step1 = -raw30286step0 := by apply Matrix.ext; change ∀ i j, raw30286step1 i j = -(raw30286step0 i j); unfold raw30286step1 raw30286step0; decide +kernel
      have hl : raw30286step1Labels = raw30286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30286step1 raw30286step1Labels = mixedMoment B raw30286step2 raw30286step2Labels := by
      have ha : raw30286step2 = raw30286step1 := by apply Matrix.ext; unfold raw30286step2 raw30286step1; decide +kernel
      have hl : raw30286step1Labels = labelEmbedding1 ∘ raw30286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30286step1 raw30286step1Labels raw30286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

def raw30287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw30287step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30287 raw30287Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw30287 raw30287Labels = mixedMoment B raw30287step0 raw30287step0Labels := by
      have ha : raw30287step0 = (fun i j => raw30287 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30287step0 raw30287; decide +kernel
      have hl : raw30287step0Labels = raw30287Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30287 raw30287Labels permutation162 permutation7
    mixedMoment B raw30287step0 raw30287step0Labels = mixedMoment B raw30287step1 raw30287step1Labels := by
      have ha : raw30287step1 = -raw30287step0 := by apply Matrix.ext; change ∀ i j, raw30287step1 i j = -(raw30287step0 i j); unfold raw30287step1 raw30287step0; decide +kernel
      have hl : raw30287step1Labels = raw30287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30287step1 raw30287step1Labels = mixedMoment B raw30287step2 raw30287step2Labels := by
      have ha : raw30287step2 = raw30287step1 := by apply Matrix.ext; unfold raw30287step2 raw30287step1; decide +kernel
      have hl : raw30287step1Labels = labelEmbedding1 ∘ raw30287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30287step1 raw30287step1Labels raw30287step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw30288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30288step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30288step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30288 raw30288Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw30288 raw30288Labels = mixedMoment B raw30288step0 raw30288step0Labels := by
      have ha : raw30288step0 = (fun i j => raw30288 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30288step0 raw30288; decide +kernel
      have hl : raw30288step0Labels = raw30288Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30288 raw30288Labels permutation162 permutation7
    mixedMoment B raw30288step0 raw30288step0Labels = mixedMoment B raw30288step1 raw30288step1Labels := by
      have ha : raw30288step1 = -raw30288step0 := by apply Matrix.ext; change ∀ i j, raw30288step1 i j = -(raw30288step0 i j); unfold raw30288step1 raw30288step0; decide +kernel
      have hl : raw30288step1Labels = raw30288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30288step1 raw30288step1Labels = mixedMoment B raw30288step2 raw30288step2Labels := by
      have ha : raw30288step2 = raw30288step1 := by apply Matrix.ext; unfold raw30288step2 raw30288step1; decide +kernel
      have hl : raw30288step1Labels = labelEmbedding1 ∘ raw30288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30288step1 raw30288step1Labels raw30288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

def raw30289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30289step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw30289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30289step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30289 raw30289Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw30289 raw30289Labels = mixedMoment B raw30289step0 raw30289step0Labels := by
      have hz : ∀ j, raw30289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30289step0 = (fun i j => raw30289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30289step0 raw30289; decide +kernel
      have hl : raw30289step0Labels = raw30289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30289 raw30289Labels permutation434 hz
    mixedMoment B raw30289step0 raw30289step0Labels = mixedMoment B raw30289step1 raw30289step1Labels := by
      have ha : raw30289step1 = (fun i j => raw30289step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30289step1 raw30289step0; decide +kernel
      have hl : raw30289step1Labels = raw30289step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30289step0 raw30289step0Labels permutation36 permutation7
    mixedMoment B raw30289step1 raw30289step1Labels = mixedMoment B raw30289step2 raw30289step2Labels := by
      have ha : raw30289step2 = -raw30289step1 := by apply Matrix.ext; change ∀ i j, raw30289step2 i j = -(raw30289step1 i j); unfold raw30289step2 raw30289step1; decide +kernel
      have hl : raw30289step2Labels = raw30289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30289step2 raw30289step2Labels = mixedMoment B raw30289step3 raw30289step3Labels := by
      have ha : raw30289step3 = raw30289step2 := by apply Matrix.ext; unfold raw30289step3 raw30289step2; decide +kernel
      have hl : raw30289step2Labels = labelEmbedding1 ∘ raw30289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30289step2 raw30289step2Labels raw30289step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

def raw30290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw30290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30290step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30290 raw30290Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw30290 raw30290Labels = mixedMoment B raw30290step0 raw30290step0Labels := by
      have hz : ∀ j, raw30290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30290step0 = (fun i j => raw30290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30290step0 raw30290; decide +kernel
      have hl : raw30290step0Labels = raw30290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30290 raw30290Labels permutation434 hz
    mixedMoment B raw30290step0 raw30290step0Labels = mixedMoment B raw30290step1 raw30290step1Labels := by
      have ha : raw30290step1 = (fun i j => raw30290step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30290step1 raw30290step0; decide +kernel
      have hl : raw30290step1Labels = raw30290step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30290step0 raw30290step0Labels permutation36 permutation7
    mixedMoment B raw30290step1 raw30290step1Labels = mixedMoment B raw30290step2 raw30290step2Labels := by
      have ha : raw30290step2 = -raw30290step1 := by apply Matrix.ext; change ∀ i j, raw30290step2 i j = -(raw30290step1 i j); unfold raw30290step2 raw30290step1; decide +kernel
      have hl : raw30290step2Labels = raw30290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30290step2 raw30290step2Labels = mixedMoment B raw30290step3 raw30290step3Labels := by
      have ha : raw30290step3 = raw30290step2 := by apply Matrix.ext; unfold raw30290step3 raw30290step2; decide +kernel
      have hl : raw30290step2Labels = labelEmbedding1 ∘ raw30290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30290step2 raw30290step2Labels raw30290step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

def raw30291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30291step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30291step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30291step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30291 raw30291Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw30291 raw30291Labels = mixedMoment B raw30291step0 raw30291step0Labels := by
      have hz : ∀ j, raw30291 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30291step0 = (fun i j => raw30291 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30291step0 raw30291; decide +kernel
      have hl : raw30291step0Labels = raw30291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30291 raw30291Labels permutation434 hz
    mixedMoment B raw30291step0 raw30291step0Labels = mixedMoment B raw30291step1 raw30291step1Labels := by
      have ha : raw30291step1 = (fun i j => raw30291step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30291step1 raw30291step0; decide +kernel
      have hl : raw30291step1Labels = raw30291step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30291step0 raw30291step0Labels permutation36 permutation7
    mixedMoment B raw30291step1 raw30291step1Labels = mixedMoment B raw30291step2 raw30291step2Labels := by
      have ha : raw30291step2 = -raw30291step1 := by apply Matrix.ext; change ∀ i j, raw30291step2 i j = -(raw30291step1 i j); unfold raw30291step2 raw30291step1; decide +kernel
      have hl : raw30291step2Labels = raw30291step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30291step2 raw30291step2Labels = mixedMoment B raw30291step3 raw30291step3Labels := by
      have ha : raw30291step3 = raw30291step2 := by apply Matrix.ext; unfold raw30291step3 raw30291step2; decide +kernel
      have hl : raw30291step2Labels = labelEmbedding1 ∘ raw30291step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30291step2 raw30291step2Labels raw30291step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

def raw30292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw30292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30292 raw30292Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw30292 raw30292Labels = mixedMoment B raw30292step0 raw30292step0Labels := by
      have ha : raw30292step0 = (fun i j => raw30292 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30292step0 raw30292; decide +kernel
      have hl : raw30292step0Labels = raw30292Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30292 raw30292Labels permutation162 permutation7
    mixedMoment B raw30292step0 raw30292step0Labels = mixedMoment B raw30292step1 raw30292step1Labels := by
      have ha : raw30292step1 = -raw30292step0 := by apply Matrix.ext; change ∀ i j, raw30292step1 i j = -(raw30292step0 i j); unfold raw30292step1 raw30292step0; decide +kernel
      have hl : raw30292step1Labels = raw30292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30292step1 raw30292step1Labels = mixedMoment B raw30292step2 raw30292step2Labels := by
      have ha : raw30292step2 = raw30292step1 := by apply Matrix.ext; unfold raw30292step2 raw30292step1; decide +kernel
      have hl : raw30292step1Labels = labelEmbedding1 ∘ raw30292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30292step1 raw30292step1Labels raw30292step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

def raw30293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw30293step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30293step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30293 raw30293Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw30293 raw30293Labels = mixedMoment B raw30293step0 raw30293step0Labels := by
      have hz : ∀ j, raw30293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30293step0 = (fun i j => raw30293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30293step0 raw30293; decide +kernel
      have hl : raw30293step0Labels = raw30293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30293 raw30293Labels permutation434 hz
    mixedMoment B raw30293step0 raw30293step0Labels = mixedMoment B raw30293step1 raw30293step1Labels := by
      have ha : raw30293step1 = (fun i j => raw30293step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30293step1 raw30293step0; decide +kernel
      have hl : raw30293step1Labels = raw30293step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30293step0 raw30293step0Labels permutation36 permutation7
    mixedMoment B raw30293step1 raw30293step1Labels = mixedMoment B raw30293step2 raw30293step2Labels := by
      have ha : raw30293step2 = -raw30293step1 := by apply Matrix.ext; change ∀ i j, raw30293step2 i j = -(raw30293step1 i j); unfold raw30293step2 raw30293step1; decide +kernel
      have hl : raw30293step2Labels = raw30293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30293step2 raw30293step2Labels = mixedMoment B raw30293step3 raw30293step3Labels := by
      have ha : raw30293step3 = raw30293step2 := by apply Matrix.ext; unfold raw30293step3 raw30293step2; decide +kernel
      have hl : raw30293step2Labels = labelEmbedding1 ∘ raw30293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30293step2 raw30293step2Labels raw30293step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw30294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30294step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw30294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw30294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30294 raw30294Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw30294 raw30294Labels = mixedMoment B raw30294step0 raw30294step0Labels := by
      have hz : ∀ j, raw30294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30294step0 = (fun i j => raw30294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30294step0 raw30294; decide +kernel
      have hl : raw30294step0Labels = raw30294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30294 raw30294Labels permutation434 hz
    mixedMoment B raw30294step0 raw30294step0Labels = mixedMoment B raw30294step1 raw30294step1Labels := by
      have ha : raw30294step1 = (fun i j => raw30294step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30294step1 raw30294step0; decide +kernel
      have hl : raw30294step1Labels = raw30294step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30294step0 raw30294step0Labels permutation149 permutation5
    mixedMoment B raw30294step1 raw30294step1Labels = mixedMoment B raw30294step2 raw30294step2Labels := by
      have ha : raw30294step2 = raw30294step1 := by apply Matrix.ext; unfold raw30294step2 raw30294step1; decide +kernel
      have hl : raw30294step1Labels = labelEmbedding1 ∘ raw30294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30294step1 raw30294step1Labels raw30294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

def raw30295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30295step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30295 raw30295Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw30295 raw30295Labels = mixedMoment B raw30295step0 raw30295step0Labels := by
      have hz : ∀ j, raw30295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30295step0 = (fun i j => raw30295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30295step0 raw30295; decide +kernel
      have hl : raw30295step0Labels = raw30295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30295 raw30295Labels permutation434 hz
    mixedMoment B raw30295step0 raw30295step0Labels = mixedMoment B raw30295step1 raw30295step1Labels := by
      have ha : raw30295step1 = (fun i j => raw30295step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30295step1 raw30295step0; decide +kernel
      have hl : raw30295step1Labels = raw30295step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30295step0 raw30295step0Labels permutation151 permutation5
    mixedMoment B raw30295step1 raw30295step1Labels = mixedMoment B raw30295step2 raw30295step2Labels := by
      have ha : raw30295step2 = raw30295step1 := by apply Matrix.ext; unfold raw30295step2 raw30295step1; decide +kernel
      have hl : raw30295step1Labels = labelEmbedding1 ∘ raw30295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30295step1 raw30295step1Labels raw30295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

def raw30296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30296step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30296step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30296 raw30296Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw30296 raw30296Labels = mixedMoment B raw30296step0 raw30296step0Labels := by
      have hz : ∀ j, raw30296 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30296step0 = (fun i j => raw30296 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30296step0 raw30296; decide +kernel
      have hl : raw30296step0Labels = raw30296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30296 raw30296Labels permutation434 hz
    mixedMoment B raw30296step0 raw30296step0Labels = mixedMoment B raw30296step1 raw30296step1Labels := by
      have ha : raw30296step1 = (fun i j => raw30296step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30296step1 raw30296step0; decide +kernel
      have hl : raw30296step1Labels = raw30296step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30296step0 raw30296step0Labels permutation148 permutation5
    mixedMoment B raw30296step1 raw30296step1Labels = mixedMoment B raw30296step2 raw30296step2Labels := by
      have ha : raw30296step2 = raw30296step1 := by apply Matrix.ext; unfold raw30296step2 raw30296step1; decide +kernel
      have hl : raw30296step1Labels = labelEmbedding1 ∘ raw30296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30296step1 raw30296step1Labels raw30296step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

def raw30297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw30297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30297 raw30297Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw30297 raw30297Labels = mixedMoment B raw30297step0 raw30297step0Labels := by
      have ha : raw30297step0 = (fun i j => raw30297 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30297step0 raw30297; decide +kernel
      have hl : raw30297step0Labels = raw30297Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30297 raw30297Labels permutation674 permutation5
    mixedMoment B raw30297step0 raw30297step0Labels = mixedMoment B raw30297step1 raw30297step1Labels := by
      have ha : raw30297step1 = raw30297step0 := by apply Matrix.ext; unfold raw30297step1 raw30297step0; decide +kernel
      have hl : raw30297step0Labels = labelEmbedding1 ∘ raw30297step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30297step0 raw30297step0Labels raw30297step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

def raw30298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw30298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw30298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30298 raw30298Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw30298 raw30298Labels = mixedMoment B raw30298step0 raw30298step0Labels := by
      have hz : ∀ j, raw30298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30298step0 = (fun i j => raw30298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30298step0 raw30298; decide +kernel
      have hl : raw30298step0Labels = raw30298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30298 raw30298Labels permutation434 hz
    mixedMoment B raw30298step0 raw30298step0Labels = mixedMoment B raw30298step1 raw30298step1Labels := by
      have ha : raw30298step1 = (fun i j => raw30298step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30298step1 raw30298step0; decide +kernel
      have hl : raw30298step1Labels = raw30298step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30298step0 raw30298step0Labels permutation139 permutation5
    mixedMoment B raw30298step1 raw30298step1Labels = mixedMoment B raw30298step2 raw30298step2Labels := by
      have ha : raw30298step2 = raw30298step1 := by apply Matrix.ext; unfold raw30298step2 raw30298step1; decide +kernel
      have hl : raw30298step1Labels = labelEmbedding1 ∘ raw30298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30298step1 raw30298step1Labels raw30298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw30299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30299 raw30299Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw30299 raw30299Labels = mixedMoment B raw30299step0 raw30299step0Labels := by
      have hz : ∀ j, raw30299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30299step0 = (fun i j => raw30299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30299step0 raw30299; decide +kernel
      have hl : raw30299step0Labels = raw30299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30299 raw30299Labels permutation434 hz
    mixedMoment B raw30299step0 raw30299step0Labels = mixedMoment B raw30299step1 raw30299step1Labels := by
      have ha : raw30299step1 = (fun i j => raw30299step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30299step1 raw30299step0; decide +kernel
      have hl : raw30299step1Labels = raw30299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30299step0 raw30299step0Labels permutation33 permutation2
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw30300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30300 raw30300Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw30300 raw30300Labels = mixedMoment B raw30300step0 raw30300step0Labels := by
      have hz : ∀ j, raw30300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30300step0 = (fun i j => raw30300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30300step0 raw30300; decide +kernel
      have hl : raw30300step0Labels = raw30300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30300 raw30300Labels permutation434 hz
    mixedMoment B raw30300step0 raw30300step0Labels = mixedMoment B raw30300step1 raw30300step1Labels := by
      have ha : raw30300step1 = (fun i j => raw30300step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30300step1 raw30300step0; decide +kernel
      have hl : raw30300step1Labels = raw30300step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30300step0 raw30300step0Labels permutation33 permutation2
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw30301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30301step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30301 raw30301Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw30301 raw30301Labels = mixedMoment B raw30301step0 raw30301step0Labels := by
      have hz : ∀ j, raw30301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30301step0 = (fun i j => raw30301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30301step0 raw30301; decide +kernel
      have hl : raw30301step0Labels = raw30301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30301 raw30301Labels permutation434 hz
    mixedMoment B raw30301step0 raw30301step0Labels = mixedMoment B raw30301step1 raw30301step1Labels := by
      have ha : raw30301step1 = (fun i j => raw30301step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30301step1 raw30301step0; decide +kernel
      have hl : raw30301step1Labels = raw30301step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30301step0 raw30301step0Labels permutation33 permutation2
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw30302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30302 raw30302Labels = mixedMoment B node2321 node2321Labels := by
  calc
    mixedMoment B raw30302 raw30302Labels = mixedMoment B raw30302step0 raw30302step0Labels := by
      have ha : raw30302step0 = (fun i j => raw30302 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30302step0 raw30302; decide +kernel
      have hl : raw30302step0Labels = raw30302Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30302 raw30302Labels permutation153 permutation2
    _ = mixedMoment B node2321 node2321Labels := by rfl

def raw30303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30303 raw30303Labels = mixedMoment B node2325 node2325Labels := by
  calc
    mixedMoment B raw30303 raw30303Labels = mixedMoment B raw30303step0 raw30303step0Labels := by
      have hz : ∀ j, raw30303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30303step0 = (fun i j => raw30303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30303step0 raw30303; decide +kernel
      have hl : raw30303step0Labels = raw30303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30303 raw30303Labels permutation434 hz
    mixedMoment B raw30303step0 raw30303step0Labels = mixedMoment B raw30303step1 raw30303step1Labels := by
      have ha : raw30303step1 = (fun i j => raw30303step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30303step1 raw30303step0; decide +kernel
      have hl : raw30303step1Labels = raw30303step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30303step0 raw30303step0Labels permutation33 permutation2
    _ = mixedMoment B node2325 node2325Labels := by rfl

def raw30304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30304 raw30304Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw30304 raw30304Labels = mixedMoment B raw30304step0 raw30304step0Labels := by
      have hz : ∀ j, raw30304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30304step0 = (fun i j => raw30304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30304step0 raw30304; decide +kernel
      have hl : raw30304step0Labels = raw30304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30304 raw30304Labels permutation434 hz
    _ = mixedMoment B node2327 node2327Labels := by rfl

def raw30305 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]
def raw30305Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30305step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw30305step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30305step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw30305step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30305 raw30305Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw30305 raw30305Labels = mixedMoment B raw30305step0 raw30305step0Labels := by
      have hz : ∀ j, raw30305 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw30305step0 = (fun i j => raw30305 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw30305step0 raw30305; decide +kernel
      have hl : raw30305step0Labels = raw30305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30305 raw30305Labels permutation590 hz
    mixedMoment B raw30305step0 raw30305step0Labels = mixedMoment B raw30305step1 raw30305step1Labels := by
      have hz : ∀ j, raw30305step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw30305step1 = (fun i j => raw30305step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw30305step1 raw30305step0; decide +kernel
      have hl : raw30305step1Labels = raw30305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30305step0 raw30305step0Labels permutation104 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw30306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30306step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30306 raw30306Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw30306 raw30306Labels = mixedMoment B raw30306step0 raw30306step0Labels := by
      have hz : ∀ j, raw30306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30306step0 = (fun i j => raw30306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30306step0 raw30306; decide +kernel
      have hl : raw30306step0Labels = raw30306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30306 raw30306Labels permutation434 hz
    mixedMoment B raw30306step0 raw30306step0Labels = mixedMoment B raw30306step1 raw30306step1Labels := by
      have ha : raw30306step1 = (fun i j => raw30306step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30306step1 raw30306step0; decide +kernel
      have hl : raw30306step1Labels = raw30306step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30306step0 raw30306step0Labels permutation57 permutation3
    mixedMoment B raw30306step1 raw30306step1Labels = mixedMoment B raw30306step2 raw30306step2Labels := by
      have ha : raw30306step2 = raw30306step1 := by apply Matrix.ext; unfold raw30306step2 raw30306step1; decide +kernel
      have hl : raw30306step1Labels = labelEmbedding6 ∘ raw30306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30306step1 raw30306step1Labels raw30306step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw30307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw30307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30307 raw30307Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw30307 raw30307Labels = mixedMoment B raw30307step0 raw30307step0Labels := by
      have hz : ∀ j, raw30307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30307step0 = (fun i j => raw30307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30307step0 raw30307; decide +kernel
      have hl : raw30307step0Labels = raw30307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30307 raw30307Labels permutation434 hz
    mixedMoment B raw30307step0 raw30307step0Labels = mixedMoment B raw30307step1 raw30307step1Labels := by
      have ha : raw30307step1 = (fun i j => raw30307step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30307step1 raw30307step0; decide +kernel
      have hl : raw30307step1Labels = raw30307step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30307step0 raw30307step0Labels permutation149 permutation2
    mixedMoment B raw30307step1 raw30307step1Labels = mixedMoment B raw30307step2 raw30307step2Labels := by
      have ha : raw30307step2 = -raw30307step1 := by apply Matrix.ext; change ∀ i j, raw30307step2 i j = -(raw30307step1 i j); unfold raw30307step2 raw30307step1; decide +kernel
      have hl : raw30307step2Labels = raw30307step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw30308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw30308step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30308step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30308step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30308step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30308 raw30308Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw30308 raw30308Labels = mixedMoment B raw30308step0 raw30308step0Labels := by
      have ha : raw30308step0 = (fun i j => raw30308 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30308step0 raw30308; decide +kernel
      have hl : raw30308step0Labels = raw30308Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30308 raw30308Labels permutation582 permutation3
    mixedMoment B raw30308step0 raw30308step0Labels = mixedMoment B raw30308step1 raw30308step1Labels := by
      have ha : raw30308step1 = -raw30308step0 := by apply Matrix.ext; change ∀ i j, raw30308step1 i j = -(raw30308step0 i j); unfold raw30308step1 raw30308step0; decide +kernel
      have hl : raw30308step1Labels = raw30308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30308step1 raw30308step1Labels = mixedMoment B raw30308step2 raw30308step2Labels := by
      have ha : raw30308step2 = raw30308step1 := by apply Matrix.ext; unfold raw30308step2 raw30308step1; decide +kernel
      have hl : raw30308step1Labels = labelEmbedding6 ∘ raw30308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30308step1 raw30308step1Labels raw30308step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw30309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30309step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30309step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30309step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30309 raw30309Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw30309 raw30309Labels = mixedMoment B raw30309step0 raw30309step0Labels := by
      have hz : ∀ j, raw30309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30309step0 = (fun i j => raw30309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30309step0 raw30309; decide +kernel
      have hl : raw30309step0Labels = raw30309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30309 raw30309Labels permutation434 hz
    mixedMoment B raw30309step0 raw30309step0Labels = mixedMoment B raw30309step1 raw30309step1Labels := by
      have hz : ∀ j, raw30309step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30309step1 = (fun i j => raw30309step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30309step1 raw30309step0; decide +kernel
      have hl : raw30309step1Labels = raw30309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30309step0 raw30309step0Labels permutation56 hz
    mixedMoment B raw30309step1 raw30309step1Labels = mixedMoment B raw30309step2 raw30309step2Labels := by
      have ha : raw30309step2 = (fun i j => raw30309step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30309step2 raw30309step1; decide +kernel
      have hl : raw30309step2Labels = raw30309step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30309step1 raw30309step1Labels permutation9 permutation3
    mixedMoment B raw30309step2 raw30309step2Labels = mixedMoment B raw30309step3 raw30309step3Labels := by
      have ha : raw30309step3 = raw30309step2 := by apply Matrix.ext; unfold raw30309step3 raw30309step2; decide +kernel
      have hl : raw30309step2Labels = labelEmbedding6 ∘ raw30309step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30309step2 raw30309step2Labels raw30309step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw30310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30310step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30310step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30310step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30310 raw30310Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw30310 raw30310Labels = mixedMoment B raw30310step0 raw30310step0Labels := by
      have hz : ∀ j, raw30310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30310step0 = (fun i j => raw30310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30310step0 raw30310; decide +kernel
      have hl : raw30310step0Labels = raw30310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30310 raw30310Labels permutation434 hz
    mixedMoment B raw30310step0 raw30310step0Labels = mixedMoment B raw30310step1 raw30310step1Labels := by
      have hz : ∀ j, raw30310step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30310step1 = (fun i j => raw30310step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30310step1 raw30310step0; decide +kernel
      have hl : raw30310step1Labels = raw30310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30310step0 raw30310step0Labels permutation56 hz
    mixedMoment B raw30310step1 raw30310step1Labels = mixedMoment B raw30310step2 raw30310step2Labels := by
      have ha : raw30310step2 = (fun i j => raw30310step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30310step2 raw30310step1; decide +kernel
      have hl : raw30310step2Labels = raw30310step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30310step1 raw30310step1Labels permutation9 permutation3
    mixedMoment B raw30310step2 raw30310step2Labels = mixedMoment B raw30310step3 raw30310step3Labels := by
      have ha : raw30310step3 = raw30310step2 := by apply Matrix.ext; unfold raw30310step3 raw30310step2; decide +kernel
      have hl : raw30310step2Labels = labelEmbedding6 ∘ raw30310step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30310step2 raw30310step2Labels raw30310step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw30311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30311step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30311 raw30311Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw30311 raw30311Labels = mixedMoment B raw30311step0 raw30311step0Labels := by
      have hz : ∀ j, raw30311 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw30311step0 = (fun i j => raw30311 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw30311step0 raw30311; decide +kernel
      have hl : raw30311step0Labels = raw30311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30311 raw30311Labels permutation265 hz
    mixedMoment B raw30311step0 raw30311step0Labels = mixedMoment B raw30311step1 raw30311step1Labels := by
      have ha : raw30311step1 = (fun i j => raw30311step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30311step1 raw30311step0; decide +kernel
      have hl : raw30311step1Labels = raw30311step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30311step0 raw30311step0Labels permutation39 permutation3
    mixedMoment B raw30311step1 raw30311step1Labels = mixedMoment B raw30311step2 raw30311step2Labels := by
      have ha : raw30311step2 = raw30311step1 := by apply Matrix.ext; unfold raw30311step2 raw30311step1; decide +kernel
      have hl : raw30311step1Labels = labelEmbedding6 ∘ raw30311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30311step1 raw30311step1Labels raw30311step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw30312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw30312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw30312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw30312step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw30312step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30312 raw30312Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw30312 raw30312Labels = mixedMoment B raw30312step0 raw30312step0Labels := by
      have hz : ∀ j, raw30312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30312step0 = (fun i j => raw30312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30312step0 raw30312; decide +kernel
      have hl : raw30312step0Labels = raw30312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30312 raw30312Labels permutation434 hz
    mixedMoment B raw30312step0 raw30312step0Labels = mixedMoment B raw30312step1 raw30312step1Labels := by
      have hz : ∀ j, raw30312step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30312step1 = (fun i j => raw30312step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30312step1 raw30312step0; decide +kernel
      have hl : raw30312step1Labels = raw30312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30312step0 raw30312step0Labels permutation56 hz
    mixedMoment B raw30312step1 raw30312step1Labels = mixedMoment B raw30312step2 raw30312step2Labels := by
      have ha : raw30312step2 = (fun i j => raw30312step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30312step2 raw30312step1; decide +kernel
      have hl : raw30312step2Labels = raw30312step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30312step1 raw30312step1Labels permutation8 permutation3
    mixedMoment B raw30312step2 raw30312step2Labels = mixedMoment B raw30312step3 raw30312step3Labels := by
      have ha : raw30312step3 = raw30312step2 := by apply Matrix.ext; unfold raw30312step3 raw30312step2; decide +kernel
      have hl : raw30312step2Labels = labelEmbedding6 ∘ raw30312step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30312step2 raw30312step2Labels raw30312step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw30313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw30313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw30313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw30313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30313step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30313step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30313step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30313 raw30313Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw30313 raw30313Labels = mixedMoment B raw30313step0 raw30313step0Labels := by
      have hz : ∀ j, raw30313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30313step0 = (fun i j => raw30313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30313step0 raw30313; decide +kernel
      have hl : raw30313step0Labels = raw30313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30313 raw30313Labels permutation434 hz
    mixedMoment B raw30313step0 raw30313step0Labels = mixedMoment B raw30313step1 raw30313step1Labels := by
      have hz : ∀ j, raw30313step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30313step1 = (fun i j => raw30313step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30313step1 raw30313step0; decide +kernel
      have hl : raw30313step1Labels = raw30313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30313step0 raw30313step0Labels permutation56 hz
    mixedMoment B raw30313step1 raw30313step1Labels = mixedMoment B raw30313step2 raw30313step2Labels := by
      have ha : raw30313step2 = (fun i j => raw30313step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30313step2 raw30313step1; decide +kernel
      have hl : raw30313step2Labels = raw30313step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30313step1 raw30313step1Labels permutation9 permutation3
    mixedMoment B raw30313step2 raw30313step2Labels = mixedMoment B raw30313step3 raw30313step3Labels := by
      have ha : raw30313step3 = raw30313step2 := by apply Matrix.ext; unfold raw30313step3 raw30313step2; decide +kernel
      have hl : raw30313step2Labels = labelEmbedding6 ∘ raw30313step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30313step2 raw30313step2Labels raw30313step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw30314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30314step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30314 raw30314Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw30314 raw30314Labels = mixedMoment B raw30314step0 raw30314step0Labels := by
      have hz : ∀ j, raw30314 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30314step0 = (fun i j => raw30314 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30314step0 raw30314; decide +kernel
      have hl : raw30314step0Labels = raw30314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30314 raw30314Labels permutation434 hz
    mixedMoment B raw30314step0 raw30314step0Labels = mixedMoment B raw30314step1 raw30314step1Labels := by
      have ha : raw30314step1 = (fun i j => raw30314step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30314step1 raw30314step0; decide +kernel
      have hl : raw30314step1Labels = raw30314step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30314step0 raw30314step0Labels permutation33 permutation3
    mixedMoment B raw30314step1 raw30314step1Labels = mixedMoment B raw30314step2 raw30314step2Labels := by
      have ha : raw30314step2 = raw30314step1 := by apply Matrix.ext; unfold raw30314step2 raw30314step1; decide +kernel
      have hl : raw30314step1Labels = labelEmbedding6 ∘ raw30314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30314step1 raw30314step1Labels raw30314step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

def raw30315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30315step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30315 raw30315Labels = mixedMoment B node4922 node4922Labels := by
  calc
    mixedMoment B raw30315 raw30315Labels = mixedMoment B raw30315step0 raw30315step0Labels := by
      have hz : ∀ j, raw30315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30315step0 = (fun i j => raw30315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30315step0 raw30315; decide +kernel
      have hl : raw30315step0Labels = raw30315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30315 raw30315Labels permutation434 hz
    mixedMoment B raw30315step0 raw30315step0Labels = mixedMoment B raw30315step1 raw30315step1Labels := by
      have ha : raw30315step1 = (fun i j => raw30315step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30315step1 raw30315step0; decide +kernel
      have hl : raw30315step1Labels = raw30315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30315step0 raw30315step0Labels permutation33 permutation3
    mixedMoment B raw30315step1 raw30315step1Labels = mixedMoment B raw30315step2 raw30315step2Labels := by
      have ha : raw30315step2 = raw30315step1 := by apply Matrix.ext; unfold raw30315step2 raw30315step1; decide +kernel
      have hl : raw30315step1Labels = labelEmbedding6 ∘ raw30315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30315step1 raw30315step1Labels raw30315step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4922 node4922Labels := by rfl

def raw30316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30316step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30316 raw30316Labels = mixedMoment B node5030 node5030Labels := by
  calc
    mixedMoment B raw30316 raw30316Labels = mixedMoment B raw30316step0 raw30316step0Labels := by
      have ha : raw30316step0 = (fun i j => raw30316 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30316step0 raw30316; decide +kernel
      have hl : raw30316step0Labels = raw30316Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30316 raw30316Labels permutation159 permutation3
    mixedMoment B raw30316step0 raw30316step0Labels = mixedMoment B raw30316step1 raw30316step1Labels := by
      have ha : raw30316step1 = raw30316step0 := by apply Matrix.ext; unfold raw30316step1 raw30316step0; decide +kernel
      have hl : raw30316step0Labels = labelEmbedding6 ∘ raw30316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30316step0 raw30316step0Labels raw30316step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5030 node5030Labels := by rfl

def raw30317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw30317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30317step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30317step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30317 raw30317Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw30317 raw30317Labels = mixedMoment B raw30317step0 raw30317step0Labels := by
      have hz : ∀ j, raw30317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30317step0 = (fun i j => raw30317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30317step0 raw30317; decide +kernel
      have hl : raw30317step0Labels = raw30317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30317 raw30317Labels permutation434 hz
    mixedMoment B raw30317step0 raw30317step0Labels = mixedMoment B raw30317step1 raw30317step1Labels := by
      have ha : raw30317step1 = (fun i j => raw30317step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30317step1 raw30317step0; decide +kernel
      have hl : raw30317step1Labels = raw30317step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30317step0 raw30317step0Labels permutation34 permutation3
    mixedMoment B raw30317step1 raw30317step1Labels = mixedMoment B raw30317step2 raw30317step2Labels := by
      have ha : raw30317step2 = raw30317step1 := by apply Matrix.ext; unfold raw30317step2 raw30317step1; decide +kernel
      have hl : raw30317step1Labels = labelEmbedding6 ∘ raw30317step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30317step1 raw30317step1Labels raw30317step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw30318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw30318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw30318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30318step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30318 raw30318Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw30318 raw30318Labels = mixedMoment B raw30318step0 raw30318step0Labels := by
      have hz : ∀ j, raw30318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30318step0 = (fun i j => raw30318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30318step0 raw30318; decide +kernel
      have hl : raw30318step0Labels = raw30318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30318 raw30318Labels permutation434 hz
    mixedMoment B raw30318step0 raw30318step0Labels = mixedMoment B raw30318step1 raw30318step1Labels := by
      have ha : raw30318step1 = (fun i j => raw30318step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30318step1 raw30318step0; decide +kernel
      have hl : raw30318step1Labels = raw30318step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30318step0 raw30318step0Labels permutation36 permutation3
    mixedMoment B raw30318step1 raw30318step1Labels = mixedMoment B raw30318step2 raw30318step2Labels := by
      have ha : raw30318step2 = raw30318step1 := by apply Matrix.ext; unfold raw30318step2 raw30318step1; decide +kernel
      have hl : raw30318step1Labels = labelEmbedding6 ∘ raw30318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30318step1 raw30318step1Labels raw30318step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw30319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30319step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30319 raw30319Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw30319 raw30319Labels = mixedMoment B raw30319step0 raw30319step0Labels := by
      have ha : raw30319step0 = (fun i j => raw30319 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30319step0 raw30319; decide +kernel
      have hl : raw30319step0Labels = raw30319Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30319 raw30319Labels permutation153 permutation3
    mixedMoment B raw30319step0 raw30319step0Labels = mixedMoment B raw30319step1 raw30319step1Labels := by
      have ha : raw30319step1 = raw30319step0 := by apply Matrix.ext; unfold raw30319step1 raw30319step0; decide +kernel
      have hl : raw30319step0Labels = labelEmbedding6 ∘ raw30319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30319step0 raw30319step0Labels raw30319step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

def raw30320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30320step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30320 raw30320Labels = mixedMoment B node4905 node4905Labels := by
  calc
    mixedMoment B raw30320 raw30320Labels = mixedMoment B raw30320step0 raw30320step0Labels := by
      have ha : raw30320step0 = (fun i j => raw30320 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30320step0 raw30320; decide +kernel
      have hl : raw30320step0Labels = raw30320Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30320 raw30320Labels permutation153 permutation3
    mixedMoment B raw30320step0 raw30320step0Labels = mixedMoment B raw30320step1 raw30320step1Labels := by
      have ha : raw30320step1 = raw30320step0 := by apply Matrix.ext; unfold raw30320step1 raw30320step0; decide +kernel
      have hl : raw30320step0Labels = labelEmbedding6 ∘ raw30320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30320step0 raw30320step0Labels raw30320step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4905 node4905Labels := by rfl

def raw30321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30321step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30321 raw30321Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw30321 raw30321Labels = mixedMoment B raw30321step0 raw30321step0Labels := by
      have ha : raw30321step0 = (fun i j => raw30321 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30321step0 raw30321; decide +kernel
      have hl : raw30321step0Labels = raw30321Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30321 raw30321Labels permutation153 permutation3
    mixedMoment B raw30321step0 raw30321step0Labels = mixedMoment B raw30321step1 raw30321step1Labels := by
      have ha : raw30321step1 = raw30321step0 := by apply Matrix.ext; unfold raw30321step1 raw30321step0; decide +kernel
      have hl : raw30321step0Labels = labelEmbedding6 ∘ raw30321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30321step0 raw30321step0Labels raw30321step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw30322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw30322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw30322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw30322step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30322step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw30322step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30322 raw30322Labels = mixedMoment B node4294 node4294Labels := by
  calc
    mixedMoment B raw30322 raw30322Labels = mixedMoment B raw30322step0 raw30322step0Labels := by
      have hz : ∀ j, raw30322 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30322step0 = (fun i j => raw30322 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30322step0 raw30322; decide +kernel
      have hl : raw30322step0Labels = raw30322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30322 raw30322Labels permutation434 hz
    mixedMoment B raw30322step0 raw30322step0Labels = mixedMoment B raw30322step1 raw30322step1Labels := by
      have ha : raw30322step1 = (fun i j => raw30322step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30322step1 raw30322step0; decide +kernel
      have hl : raw30322step1Labels = raw30322step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30322step0 raw30322step0Labels permutation33 permutation3
    mixedMoment B raw30322step1 raw30322step1Labels = mixedMoment B raw30322step2 raw30322step2Labels := by
      have ha : raw30322step2 = raw30322step1 := by apply Matrix.ext; unfold raw30322step2 raw30322step1; decide +kernel
      have hl : raw30322step1Labels = labelEmbedding6 ∘ raw30322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30322step1 raw30322step1Labels raw30322step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4294 node4294Labels := by rfl

def raw30323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw30323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw30323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw30323step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30323step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30323step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30323step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30323 raw30323Labels = mixedMoment B node4662 node4662Labels := by
  calc
    mixedMoment B raw30323 raw30323Labels = mixedMoment B raw30323step0 raw30323step0Labels := by
      have hz : ∀ j, raw30323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30323step0 = (fun i j => raw30323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30323step0 raw30323; decide +kernel
      have hl : raw30323step0Labels = raw30323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30323 raw30323Labels permutation434 hz
    mixedMoment B raw30323step0 raw30323step0Labels = mixedMoment B raw30323step1 raw30323step1Labels := by
      have ha : raw30323step1 = (fun i j => raw30323step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30323step1 raw30323step0; decide +kernel
      have hl : raw30323step1Labels = raw30323step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30323step0 raw30323step0Labels permutation127 permutation3
    mixedMoment B raw30323step1 raw30323step1Labels = mixedMoment B raw30323step2 raw30323step2Labels := by
      have ha : raw30323step2 = -raw30323step1 := by apply Matrix.ext; change ∀ i j, raw30323step2 i j = -(raw30323step1 i j); unfold raw30323step2 raw30323step1; decide +kernel
      have hl : raw30323step2Labels = raw30323step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30323step2 raw30323step2Labels = mixedMoment B raw30323step3 raw30323step3Labels := by
      have ha : raw30323step3 = raw30323step2 := by apply Matrix.ext; unfold raw30323step3 raw30323step2; decide +kernel
      have hl : raw30323step2Labels = labelEmbedding6 ∘ raw30323step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30323step2 raw30323step2Labels raw30323step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4662 node4662Labels := by rfl

def raw30324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw30324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw30324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30324step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30324step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30324step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30324step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30324 raw30324Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw30324 raw30324Labels = mixedMoment B raw30324step0 raw30324step0Labels := by
      have hz : ∀ j, raw30324 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30324step0 = (fun i j => raw30324 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30324step0 raw30324; decide +kernel
      have hl : raw30324step0Labels = raw30324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30324 raw30324Labels permutation434 hz
    mixedMoment B raw30324step0 raw30324step0Labels = mixedMoment B raw30324step1 raw30324step1Labels := by
      have ha : raw30324step1 = (fun i j => raw30324step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30324step1 raw30324step0; decide +kernel
      have hl : raw30324step1Labels = raw30324step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30324step0 raw30324step0Labels permutation127 permutation3
    mixedMoment B raw30324step1 raw30324step1Labels = mixedMoment B raw30324step2 raw30324step2Labels := by
      have ha : raw30324step2 = -raw30324step1 := by apply Matrix.ext; change ∀ i j, raw30324step2 i j = -(raw30324step1 i j); unfold raw30324step2 raw30324step1; decide +kernel
      have hl : raw30324step2Labels = raw30324step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30324step2 raw30324step2Labels = mixedMoment B raw30324step3 raw30324step3Labels := by
      have ha : raw30324step3 = raw30324step2 := by apply Matrix.ext; unfold raw30324step3 raw30324step2; decide +kernel
      have hl : raw30324step2Labels = labelEmbedding6 ∘ raw30324step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30324step2 raw30324step2Labels raw30324step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw30325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw30325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30325step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30325step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30325step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30325 raw30325Labels = mixedMoment B node4660 node4660Labels := by
  calc
    mixedMoment B raw30325 raw30325Labels = mixedMoment B raw30325step0 raw30325step0Labels := by
      have ha : raw30325step0 = (fun i j => raw30325 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30325step0 raw30325; decide +kernel
      have hl : raw30325step0Labels = raw30325Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30325 raw30325Labels permutation582 permutation3
    mixedMoment B raw30325step0 raw30325step0Labels = mixedMoment B raw30325step1 raw30325step1Labels := by
      have ha : raw30325step1 = -raw30325step0 := by apply Matrix.ext; change ∀ i j, raw30325step1 i j = -(raw30325step0 i j); unfold raw30325step1 raw30325step0; decide +kernel
      have hl : raw30325step1Labels = raw30325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30325step1 raw30325step1Labels = mixedMoment B raw30325step2 raw30325step2Labels := by
      have ha : raw30325step2 = raw30325step1 := by apply Matrix.ext; unfold raw30325step2 raw30325step1; decide +kernel
      have hl : raw30325step1Labels = labelEmbedding6 ∘ raw30325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30325step1 raw30325step1Labels raw30325step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4660 node4660Labels := by rfl

def raw30326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw30326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw30326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30326step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30326step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30326 raw30326Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw30326 raw30326Labels = mixedMoment B raw30326step0 raw30326step0Labels := by
      have hz : ∀ j, raw30326 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30326step0 = (fun i j => raw30326 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30326step0 raw30326; decide +kernel
      have hl : raw30326step0Labels = raw30326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30326 raw30326Labels permutation434 hz
    mixedMoment B raw30326step0 raw30326step0Labels = mixedMoment B raw30326step1 raw30326step1Labels := by
      have ha : raw30326step1 = (fun i j => raw30326step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30326step1 raw30326step0; decide +kernel
      have hl : raw30326step1Labels = raw30326step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30326step0 raw30326step0Labels permutation121 permutation5
    mixedMoment B raw30326step1 raw30326step1Labels = mixedMoment B raw30326step2 raw30326step2Labels := by
      have ha : raw30326step2 = raw30326step1 := by apply Matrix.ext; unfold raw30326step2 raw30326step1; decide +kernel
      have hl : raw30326step1Labels = labelEmbedding8 ∘ raw30326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30326step1 raw30326step1Labels raw30326step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw30327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw30327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw30327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30327step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30327step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30327 raw30327Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw30327 raw30327Labels = mixedMoment B raw30327step0 raw30327step0Labels := by
      have hz : ∀ j, raw30327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30327step0 = (fun i j => raw30327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30327step0 raw30327; decide +kernel
      have hl : raw30327step0Labels = raw30327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30327 raw30327Labels permutation434 hz
    mixedMoment B raw30327step0 raw30327step0Labels = mixedMoment B raw30327step1 raw30327step1Labels := by
      have ha : raw30327step1 = (fun i j => raw30327step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30327step1 raw30327step0; decide +kernel
      have hl : raw30327step1Labels = raw30327step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30327step0 raw30327step0Labels permutation32 permutation3
    mixedMoment B raw30327step1 raw30327step1Labels = mixedMoment B raw30327step2 raw30327step2Labels := by
      have ha : raw30327step2 = raw30327step1 := by apply Matrix.ext; unfold raw30327step2 raw30327step1; decide +kernel
      have hl : raw30327step1Labels = labelEmbedding6 ∘ raw30327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30327step1 raw30327step1Labels raw30327step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4296 node4296Labels := by rfl

def raw30328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw30328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw30328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30328step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30328step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30328 raw30328Labels = mixedMoment B node4908 node4908Labels := by
  calc
    mixedMoment B raw30328 raw30328Labels = mixedMoment B raw30328step0 raw30328step0Labels := by
      have hz : ∀ j, raw30328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30328step0 = (fun i j => raw30328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30328step0 raw30328; decide +kernel
      have hl : raw30328step0Labels = raw30328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30328 raw30328Labels permutation434 hz
    mixedMoment B raw30328step0 raw30328step0Labels = mixedMoment B raw30328step1 raw30328step1Labels := by
      have ha : raw30328step1 = (fun i j => raw30328step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30328step1 raw30328step0; decide +kernel
      have hl : raw30328step1Labels = raw30328step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30328step0 raw30328step0Labels permutation32 permutation3
    mixedMoment B raw30328step1 raw30328step1Labels = mixedMoment B raw30328step2 raw30328step2Labels := by
      have ha : raw30328step2 = raw30328step1 := by apply Matrix.ext; unfold raw30328step2 raw30328step1; decide +kernel
      have hl : raw30328step1Labels = labelEmbedding6 ∘ raw30328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30328step1 raw30328step1Labels raw30328step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4908 node4908Labels := by rfl

def raw30329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw30329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw30329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30329step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30329 raw30329Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw30329 raw30329Labels = mixedMoment B raw30329step0 raw30329step0Labels := by
      have hz : ∀ j, raw30329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30329step0 = (fun i j => raw30329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30329step0 raw30329; decide +kernel
      have hl : raw30329step0Labels = raw30329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30329 raw30329Labels permutation434 hz
    mixedMoment B raw30329step0 raw30329step0Labels = mixedMoment B raw30329step1 raw30329step1Labels := by
      have ha : raw30329step1 = (fun i j => raw30329step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30329step1 raw30329step0; decide +kernel
      have hl : raw30329step1Labels = raw30329step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30329step0 raw30329step0Labels permutation149 permutation2
    mixedMoment B raw30329step1 raw30329step1Labels = mixedMoment B raw30329step2 raw30329step2Labels := by
      have ha : raw30329step2 = -raw30329step1 := by apply Matrix.ext; change ∀ i j, raw30329step2 i j = -(raw30329step1 i j); unfold raw30329step2 raw30329step1; decide +kernel
      have hl : raw30329step2Labels = raw30329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw30330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw30330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 2, 1]]
def raw30330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw30330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30330 raw30330Labels = mixedMoment B node4960 node4960Labels := by
  calc
    mixedMoment B raw30330 raw30330Labels = mixedMoment B raw30330step0 raw30330step0Labels := by
      have ha : raw30330step0 = (fun i j => raw30330 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30330step0 raw30330; decide +kernel
      have hl : raw30330step0Labels = raw30330Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30330 raw30330Labels permutation680 permutation2
    mixedMoment B raw30330step0 raw30330step0Labels = mixedMoment B raw30330step1 raw30330step1Labels := by
      have ha : raw30330step1 = -raw30330step0 := by apply Matrix.ext; change ∀ i j, raw30330step1 i j = -(raw30330step0 i j); unfold raw30330step1 raw30330step0; decide +kernel
      have hl : raw30330step1Labels = raw30330step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4960 node4960Labels := by rfl

def raw30331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw30331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw30331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30331step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30331 raw30331Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw30331 raw30331Labels = mixedMoment B raw30331step0 raw30331step0Labels := by
      have hz : ∀ j, raw30331 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30331step0 = (fun i j => raw30331 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30331step0 raw30331; decide +kernel
      have hl : raw30331step0Labels = raw30331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30331 raw30331Labels permutation434 hz
    mixedMoment B raw30331step0 raw30331step0Labels = mixedMoment B raw30331step1 raw30331step1Labels := by
      have ha : raw30331step1 = (fun i j => raw30331step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30331step1 raw30331step0; decide +kernel
      have hl : raw30331step1Labels = raw30331step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30331step0 raw30331step0Labels permutation32 permutation3
    mixedMoment B raw30331step1 raw30331step1Labels = mixedMoment B raw30331step2 raw30331step2Labels := by
      have ha : raw30331step2 = raw30331step1 := by apply Matrix.ext; unfold raw30331step2 raw30331step1; decide +kernel
      have hl : raw30331step1Labels = labelEmbedding6 ∘ raw30331step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30331step1 raw30331step1Labels raw30331step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw30332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30332 raw30332Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw30332 raw30332Labels = mixedMoment B raw30332step0 raw30332step0Labels := by
      have hz : ∀ j, raw30332 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30332step0 = (fun i j => raw30332 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30332step0 raw30332; decide +kernel
      have hl : raw30332step0Labels = raw30332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30332 raw30332Labels permutation434 hz
    mixedMoment B raw30332step0 raw30332step0Labels = mixedMoment B raw30332step1 raw30332step1Labels := by
      have ha : raw30332step1 = (fun i j => raw30332step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30332step1 raw30332step0; decide +kernel
      have hl : raw30332step1Labels = raw30332step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30332step0 raw30332step0Labels permutation57 permutation3
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw30333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw30333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30333 raw30333Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw30333 raw30333Labels = mixedMoment B raw30333step0 raw30333step0Labels := by
      have hz : ∀ j, raw30333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30333step0 = (fun i j => raw30333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30333step0 raw30333; decide +kernel
      have hl : raw30333step0Labels = raw30333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30333 raw30333Labels permutation434 hz
    mixedMoment B raw30333step0 raw30333step0Labels = mixedMoment B raw30333step1 raw30333step1Labels := by
      have ha : raw30333step1 = (fun i j => raw30333step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30333step1 raw30333step0; decide +kernel
      have hl : raw30333step1Labels = raw30333step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30333step0 raw30333step0Labels permutation127 permutation3
    mixedMoment B raw30333step1 raw30333step1Labels = mixedMoment B raw30333step2 raw30333step2Labels := by
      have ha : raw30333step2 = -raw30333step1 := by apply Matrix.ext; change ∀ i j, raw30333step2 i j = -(raw30333step1 i j); unfold raw30333step2 raw30333step1; decide +kernel
      have hl : raw30333step2Labels = raw30333step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw30334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw30334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30334 raw30334Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw30334 raw30334Labels = mixedMoment B raw30334step0 raw30334step0Labels := by
      have ha : raw30334step0 = (fun i j => raw30334 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30334step0 raw30334; decide +kernel
      have hl : raw30334step0Labels = raw30334Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30334 raw30334Labels permutation582 permutation3
    mixedMoment B raw30334step0 raw30334step0Labels = mixedMoment B raw30334step1 raw30334step1Labels := by
      have ha : raw30334step1 = -raw30334step0 := by apply Matrix.ext; change ∀ i j, raw30334step1 i j = -(raw30334step0 i j); unfold raw30334step1 raw30334step0; decide +kernel
      have hl : raw30334step1Labels = raw30334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw30335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30335step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30335 raw30335Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw30335 raw30335Labels = mixedMoment B raw30335step0 raw30335step0Labels := by
      have hz : ∀ j, raw30335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30335step0 = (fun i j => raw30335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30335step0 raw30335; decide +kernel
      have hl : raw30335step0Labels = raw30335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30335 raw30335Labels permutation434 hz
    mixedMoment B raw30335step0 raw30335step0Labels = mixedMoment B raw30335step1 raw30335step1Labels := by
      have hz : ∀ j, raw30335step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30335step1 = (fun i j => raw30335step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30335step1 raw30335step0; decide +kernel
      have hl : raw30335step1Labels = raw30335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30335step0 raw30335step0Labels permutation56 hz
    mixedMoment B raw30335step1 raw30335step1Labels = mixedMoment B raw30335step2 raw30335step2Labels := by
      have ha : raw30335step2 = (fun i j => raw30335step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30335step2 raw30335step1; decide +kernel
      have hl : raw30335step2Labels = raw30335step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30335step1 raw30335step1Labels permutation9 permutation3
    _ = mixedMoment B node1049 node1049Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
