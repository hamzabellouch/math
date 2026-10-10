import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15360 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw15360Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15360step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw15360step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15360step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw15360step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15360step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw15360step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical15360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15360 raw15360Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw15360 raw15360Labels = mixedMoment B raw15360step0 raw15360step0Labels := by
      have hz : ∀ j, raw15360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15360step0 = (fun i j => raw15360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15360step0 raw15360; decide +kernel
      have hl : raw15360step0Labels = raw15360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15360 raw15360Labels permutation346 hz
    mixedMoment B raw15360step0 raw15360step0Labels = mixedMoment B raw15360step1 raw15360step1Labels := by
      have hz : ∀ j, raw15360step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw15360step1 = (fun i j => raw15360step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw15360step1 raw15360step0; decide +kernel
      have hl : raw15360step1Labels = raw15360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15360step0 raw15360step0Labels permutation32 hz
    mixedMoment B raw15360step1 raw15360step1Labels = mixedMoment B raw15360step2 raw15360step2Labels := by
      have ha : raw15360step2 = (fun i j => raw15360step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw15360step2 raw15360step1; decide +kernel
      have hl : raw15360step2Labels = raw15360step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15360step1 raw15360step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw15361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15361 raw15361Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw15361 raw15361Labels = mixedMoment B raw15361step0 raw15361step0Labels := by
      have ha : raw15361step0 = (fun i j => raw15361 (permutation465 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15361step0 raw15361; decide +kernel
      have hl : raw15361step0Labels = raw15361Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15361 raw15361Labels permutation465 permutation4
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw15362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15362 raw15362Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw15362 raw15362Labels = mixedMoment B raw15362step0 raw15362step0Labels := by
      have hz : ∀ j, raw15362 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15362step0 = (fun i j => raw15362 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15362step0 raw15362; decide +kernel
      have hl : raw15362step0Labels = raw15362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15362 raw15362Labels permutation346 hz
    mixedMoment B raw15362step0 raw15362step0Labels = mixedMoment B raw15362step1 raw15362step1Labels := by
      have ha : raw15362step1 = (fun i j => raw15362step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15362step1 raw15362step0; decide +kernel
      have hl : raw15362step1Labels = raw15362step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15362step0 raw15362step0Labels permutation149 permutation2
    mixedMoment B raw15362step1 raw15362step1Labels = mixedMoment B raw15362step2 raw15362step2Labels := by
      have ha : raw15362step2 = -raw15362step1 := by apply Matrix.ext; change ∀ i j, raw15362step2 i j = -(raw15362step1 i j); unfold raw15362step2 raw15362step1; decide +kernel
      have hl : raw15362step2Labels = raw15362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw15363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15363 raw15363Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw15363 raw15363Labels = mixedMoment B raw15363step0 raw15363step0Labels := by
      have hz : ∀ j, raw15363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15363step0 = (fun i j => raw15363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15363step0 raw15363; decide +kernel
      have hl : raw15363step0Labels = raw15363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15363 raw15363Labels permutation346 hz
    mixedMoment B raw15363step0 raw15363step0Labels = mixedMoment B raw15363step1 raw15363step1Labels := by
      have ha : raw15363step1 = (fun i j => raw15363step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15363step1 raw15363step0; decide +kernel
      have hl : raw15363step1Labels = raw15363step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15363step0 raw15363step0Labels permutation108 permutation4
    mixedMoment B raw15363step1 raw15363step1Labels = mixedMoment B raw15363step2 raw15363step2Labels := by
      have ha : raw15363step2 = -raw15363step1 := by apply Matrix.ext; change ∀ i j, raw15363step2 i j = -(raw15363step1 i j); unfold raw15363step2 raw15363step1; decide +kernel
      have hl : raw15363step2Labels = raw15363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw15364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15364 raw15364Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw15364 raw15364Labels = mixedMoment B raw15364step0 raw15364step0Labels := by
      have hz : ∀ j, raw15364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15364step0 = (fun i j => raw15364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15364step0 raw15364; decide +kernel
      have hl : raw15364step0Labels = raw15364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15364 raw15364Labels permutation346 hz
    mixedMoment B raw15364step0 raw15364step0Labels = mixedMoment B raw15364step1 raw15364step1Labels := by
      have ha : raw15364step1 = (fun i j => raw15364step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15364step1 raw15364step0; decide +kernel
      have hl : raw15364step1Labels = raw15364step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15364step0 raw15364step0Labels permutation91 permutation4
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw15365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15365 raw15365Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw15365 raw15365Labels = mixedMoment B raw15365step0 raw15365step0Labels := by
      have hz : ∀ j, raw15365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15365step0 = (fun i j => raw15365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15365step0 raw15365; decide +kernel
      have hl : raw15365step0Labels = raw15365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15365 raw15365Labels permutation346 hz
    mixedMoment B raw15365step0 raw15365step0Labels = mixedMoment B raw15365step1 raw15365step1Labels := by
      have ha : raw15365step1 = (fun i j => raw15365step0 (permutation100 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15365step1 raw15365step0; decide +kernel
      have hl : raw15365step1Labels = raw15365step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15365step0 raw15365step0Labels permutation100 permutation4
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw15366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15366 raw15366Labels = mixedMoment B node3828 node3828Labels := by
  calc
    mixedMoment B raw15366 raw15366Labels = mixedMoment B raw15366step0 raw15366step0Labels := by
      have ha : raw15366step0 = (fun i j => raw15366 (permutation482 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15366step0 raw15366; decide +kernel
      have hl : raw15366step0Labels = raw15366Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15366 raw15366Labels permutation482 permutation4
    _ = mixedMoment B node3828 node3828Labels := by rfl

def raw15367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15367 raw15367Labels = mixedMoment B node2634 node2634Labels := by
  calc
    mixedMoment B raw15367 raw15367Labels = mixedMoment B raw15367step0 raw15367step0Labels := by
      have hz : ∀ j, raw15367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15367step0 = (fun i j => raw15367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15367step0 raw15367; decide +kernel
      have hl : raw15367step0Labels = raw15367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15367 raw15367Labels permutation346 hz
    mixedMoment B raw15367step0 raw15367step0Labels = mixedMoment B raw15367step1 raw15367step1Labels := by
      have ha : raw15367step1 = (fun i j => raw15367step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15367step1 raw15367step0; decide +kernel
      have hl : raw15367step1Labels = raw15367step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15367step0 raw15367step0Labels permutation101 permutation4
    _ = mixedMoment B node2634 node2634Labels := by rfl

def raw15368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15368 raw15368Labels = mixedMoment B node3699 node3699Labels := by
  calc
    mixedMoment B raw15368 raw15368Labels = mixedMoment B raw15368step0 raw15368step0Labels := by
      have hz : ∀ j, raw15368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15368step0 = (fun i j => raw15368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15368step0 raw15368; decide +kernel
      have hl : raw15368step0Labels = raw15368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15368 raw15368Labels permutation346 hz
    mixedMoment B raw15368step0 raw15368step0Labels = mixedMoment B raw15368step1 raw15368step1Labels := by
      have ha : raw15368step1 = (fun i j => raw15368step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15368step1 raw15368step0; decide +kernel
      have hl : raw15368step1Labels = raw15368step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15368step0 raw15368step0Labels permutation126 permutation2
    mixedMoment B raw15368step1 raw15368step1Labels = mixedMoment B raw15368step2 raw15368step2Labels := by
      have ha : raw15368step2 = -raw15368step1 := by apply Matrix.ext; change ∀ i j, raw15368step2 i j = -(raw15368step1 i j); unfold raw15368step2 raw15368step1; decide +kernel
      have hl : raw15368step2Labels = raw15368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3699 node3699Labels := by rfl

def raw15369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15369 raw15369Labels = mixedMoment B node2873 node2873Labels := by
  calc
    mixedMoment B raw15369 raw15369Labels = mixedMoment B raw15369step0 raw15369step0Labels := by
      have hz : ∀ j, raw15369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15369step0 = (fun i j => raw15369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15369step0 raw15369; decide +kernel
      have hl : raw15369step0Labels = raw15369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15369 raw15369Labels permutation346 hz
    mixedMoment B raw15369step0 raw15369step0Labels = mixedMoment B raw15369step1 raw15369step1Labels := by
      have ha : raw15369step1 = (fun i j => raw15369step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15369step1 raw15369step0; decide +kernel
      have hl : raw15369step1Labels = raw15369step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15369step0 raw15369step0Labels permutation150 permutation2
    mixedMoment B raw15369step1 raw15369step1Labels = mixedMoment B raw15369step2 raw15369step2Labels := by
      have ha : raw15369step2 = -raw15369step1 := by apply Matrix.ext; change ∀ i j, raw15369step2 i j = -(raw15369step1 i j); unfold raw15369step2 raw15369step1; decide +kernel
      have hl : raw15369step2Labels = raw15369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2873 node2873Labels := by rfl

def raw15370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15370 raw15370Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw15370 raw15370Labels = mixedMoment B raw15370step0 raw15370step0Labels := by
      have ha : raw15370step0 = (fun i j => raw15370 (permutation508 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15370step0 raw15370; decide +kernel
      have hl : raw15370step0Labels = raw15370Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15370 raw15370Labels permutation508 permutation4
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw15371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15371 raw15371Labels = mixedMoment B node2616 node2616Labels := by
  calc
    mixedMoment B raw15371 raw15371Labels = mixedMoment B raw15371step0 raw15371step0Labels := by
      have ha : raw15371step0 = (fun i j => raw15371 (permutation509 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15371step0 raw15371; decide +kernel
      have hl : raw15371step0Labels = raw15371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15371 raw15371Labels permutation509 permutation4
    _ = mixedMoment B node2616 node2616Labels := by rfl

def raw15372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15372 raw15372Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw15372 raw15372Labels = mixedMoment B raw15372step0 raw15372step0Labels := by
      have ha : raw15372step0 = (fun i j => raw15372 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15372step0 raw15372; decide +kernel
      have hl : raw15372step0Labels = raw15372Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15372 raw15372Labels permutation589 permutation2
    mixedMoment B raw15372step0 raw15372step0Labels = mixedMoment B raw15372step1 raw15372step1Labels := by
      have ha : raw15372step1 = -raw15372step0 := by apply Matrix.ext; change ∀ i j, raw15372step1 i j = -(raw15372step0 i j); unfold raw15372step1 raw15372step0; decide +kernel
      have hl : raw15372step1Labels = raw15372step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3698 node3698Labels := by rfl

def raw15373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15373 raw15373Labels = mixedMoment B node2870 node2870Labels := by
  calc
    mixedMoment B raw15373 raw15373Labels = mixedMoment B raw15373step0 raw15373step0Labels := by
      have ha : raw15373step0 = (fun i j => raw15373 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15373step0 raw15373; decide +kernel
      have hl : raw15373step0Labels = raw15373Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15373 raw15373Labels permutation688 permutation2
    mixedMoment B raw15373step0 raw15373step0Labels = mixedMoment B raw15373step1 raw15373step1Labels := by
      have ha : raw15373step1 = -raw15373step0 := by apply Matrix.ext; change ∀ i j, raw15373step1 i j = -(raw15373step0 i j); unfold raw15373step1 raw15373step0; decide +kernel
      have hl : raw15373step1Labels = raw15373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2870 node2870Labels := by rfl

def raw15374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15374 raw15374Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw15374 raw15374Labels = mixedMoment B raw15374step0 raw15374step0Labels := by
      have hz : ∀ j, raw15374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15374step0 = (fun i j => raw15374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15374step0 raw15374; decide +kernel
      have hl : raw15374step0Labels = raw15374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15374 raw15374Labels permutation346 hz
    mixedMoment B raw15374step0 raw15374step0Labels = mixedMoment B raw15374step1 raw15374step1Labels := by
      have ha : raw15374step1 = (fun i j => raw15374step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15374step1 raw15374step0; decide +kernel
      have hl : raw15374step1Labels = raw15374step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15374step0 raw15374step0Labels permutation146 permutation2
    mixedMoment B raw15374step1 raw15374step1Labels = mixedMoment B raw15374step2 raw15374step2Labels := by
      have ha : raw15374step2 = -raw15374step1 := by apply Matrix.ext; change ∀ i j, raw15374step2 i j = -(raw15374step1 i j); unfold raw15374step2 raw15374step1; decide +kernel
      have hl : raw15374step2Labels = raw15374step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw15375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15375 raw15375Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw15375 raw15375Labels = mixedMoment B raw15375step0 raw15375step0Labels := by
      have ha : raw15375step0 = (fun i j => raw15375 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15375step0 raw15375; decide +kernel
      have hl : raw15375step0Labels = raw15375Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15375 raw15375Labels permutation680 permutation2
    mixedMoment B raw15375step0 raw15375step0Labels = mixedMoment B raw15375step1 raw15375step1Labels := by
      have ha : raw15375step1 = -raw15375step0 := by apply Matrix.ext; change ∀ i j, raw15375step1 i j = -(raw15375step0 i j); unfold raw15375step1 raw15375step0; decide +kernel
      have hl : raw15375step1Labels = raw15375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw15376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15376 raw15376Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw15376 raw15376Labels = mixedMoment B raw15376step0 raw15376step0Labels := by
      have hz : ∀ j, raw15376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15376step0 = (fun i j => raw15376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15376step0 raw15376; decide +kernel
      have hl : raw15376step0Labels = raw15376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15376 raw15376Labels permutation346 hz
    mixedMoment B raw15376step0 raw15376step0Labels = mixedMoment B raw15376step1 raw15376step1Labels := by
      have ha : raw15376step1 = (fun i j => raw15376step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15376step1 raw15376step0; decide +kernel
      have hl : raw15376step1Labels = raw15376step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15376step0 raw15376step0Labels permutation125 permutation2
    mixedMoment B raw15376step1 raw15376step1Labels = mixedMoment B raw15376step2 raw15376step2Labels := by
      have ha : raw15376step2 = -raw15376step1 := by apply Matrix.ext; change ∀ i j, raw15376step2 i j = -(raw15376step1 i j); unfold raw15376step2 raw15376step1; decide +kernel
      have hl : raw15376step2Labels = raw15376step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw15377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15377step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15377 raw15377Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw15377 raw15377Labels = mixedMoment B raw15377step0 raw15377step0Labels := by
      have hz : ∀ j, raw15377 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15377step0 = (fun i j => raw15377 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15377step0 raw15377; decide +kernel
      have hl : raw15377step0Labels = raw15377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15377 raw15377Labels permutation346 hz
    mixedMoment B raw15377step0 raw15377step0Labels = mixedMoment B raw15377step1 raw15377step1Labels := by
      have ha : raw15377step1 = (fun i j => raw15377step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15377step1 raw15377step0; decide +kernel
      have hl : raw15377step1Labels = raw15377step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15377step0 raw15377step0Labels permutation149 permutation2
    mixedMoment B raw15377step1 raw15377step1Labels = mixedMoment B raw15377step2 raw15377step2Labels := by
      have ha : raw15377step2 = -raw15377step1 := by apply Matrix.ext; change ∀ i j, raw15377step2 i j = -(raw15377step1 i j); unfold raw15377step2 raw15377step1; decide +kernel
      have hl : raw15377step2Labels = raw15377step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2885 node2885Labels := by rfl

def raw15378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15378 raw15378Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw15378 raw15378Labels = mixedMoment B raw15378step0 raw15378step0Labels := by
      have hz : ∀ j, raw15378 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15378step0 = (fun i j => raw15378 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15378step0 raw15378; decide +kernel
      have hl : raw15378step0Labels = raw15378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15378 raw15378Labels permutation346 hz
    mixedMoment B raw15378step0 raw15378step0Labels = mixedMoment B raw15378step1 raw15378step1Labels := by
      have ha : raw15378step1 = (fun i j => raw15378step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15378step1 raw15378step0; decide +kernel
      have hl : raw15378step1Labels = raw15378step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15378step0 raw15378step0Labels permutation127 permutation2
    mixedMoment B raw15378step1 raw15378step1Labels = mixedMoment B raw15378step2 raw15378step2Labels := by
      have ha : raw15378step2 = -raw15378step1 := by apply Matrix.ext; change ∀ i j, raw15378step2 i j = -(raw15378step1 i j); unfold raw15378step2 raw15378step1; decide +kernel
      have hl : raw15378step2Labels = raw15378step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw15379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15379step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15379 raw15379Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15379 raw15379Labels = mixedMoment B raw15379step0 raw15379step0Labels := by
      have hz : ∀ j, raw15379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15379step0 = (fun i j => raw15379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15379step0 raw15379; decide +kernel
      have hl : raw15379step0Labels = raw15379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15379 raw15379Labels permutation346 hz
    mixedMoment B raw15379step0 raw15379step0Labels = mixedMoment B raw15379step1 raw15379step1Labels := by
      have ha : raw15379step1 = (fun i j => raw15379step0 (permutation105 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15379step1 raw15379step0; decide +kernel
      have hl : raw15379step1Labels = raw15379step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15379step0 raw15379step0Labels permutation105 permutation4
    mixedMoment B raw15379step1 raw15379step1Labels = mixedMoment B raw15379step2 raw15379step2Labels := by
      have ha : raw15379step2 = -raw15379step1 := by apply Matrix.ext; change ∀ i j, raw15379step2 i j = -(raw15379step1 i j); unfold raw15379step2 raw15379step1; decide +kernel
      have hl : raw15379step2Labels = raw15379step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw15380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw15380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15380 raw15380Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw15380 raw15380Labels = mixedMoment B raw15380step0 raw15380step0Labels := by
      have ha : raw15380step0 = (fun i j => raw15380 (permutation524 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15380step0 raw15380; decide +kernel
      have hl : raw15380step0Labels = raw15380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15380 raw15380Labels permutation524 permutation4
    mixedMoment B raw15380step0 raw15380step0Labels = mixedMoment B raw15380step1 raw15380step1Labels := by
      have ha : raw15380step1 = -raw15380step0 := by apply Matrix.ext; change ∀ i j, raw15380step1 i j = -(raw15380step0 i j); unfold raw15380step1 raw15380step0; decide +kernel
      have hl : raw15380step1Labels = raw15380step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3723 node3723Labels := by rfl

def raw15381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw15381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15381 raw15381Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw15381 raw15381Labels = mixedMoment B raw15381step0 raw15381step0Labels := by
      have hz : ∀ j, raw15381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15381step0 = (fun i j => raw15381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15381step0 raw15381; decide +kernel
      have hl : raw15381step0Labels = raw15381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15381 raw15381Labels permutation346 hz
    mixedMoment B raw15381step0 raw15381step0Labels = mixedMoment B raw15381step1 raw15381step1Labels := by
      have ha : raw15381step1 = (fun i j => raw15381step0 (permutation100 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15381step1 raw15381step0; decide +kernel
      have hl : raw15381step1Labels = raw15381step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15381step0 raw15381step0Labels permutation100 permutation4
    _ = mixedMoment B node2620 node2620Labels := by rfl

def raw15382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15382 raw15382Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw15382 raw15382Labels = mixedMoment B raw15382step0 raw15382step0Labels := by
      have hz : ∀ j, raw15382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15382step0 = (fun i j => raw15382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15382step0 raw15382; decide +kernel
      have hl : raw15382step0Labels = raw15382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15382 raw15382Labels permutation346 hz
    mixedMoment B raw15382step0 raw15382step0Labels = mixedMoment B raw15382step1 raw15382step1Labels := by
      have ha : raw15382step1 = (fun i j => raw15382step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15382step1 raw15382step0; decide +kernel
      have hl : raw15382step1Labels = raw15382step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15382step0 raw15382step0Labels permutation151 permutation2
    mixedMoment B raw15382step1 raw15382step1Labels = mixedMoment B raw15382step2 raw15382step2Labels := by
      have ha : raw15382step2 = -raw15382step1 := by apply Matrix.ext; change ∀ i j, raw15382step2 i j = -(raw15382step1 i j); unfold raw15382step2 raw15382step1; decide +kernel
      have hl : raw15382step2Labels = raw15382step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3045 node3045Labels := by rfl

def raw15383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15383step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15383step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15383step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15383step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15383 raw15383Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw15383 raw15383Labels = mixedMoment B raw15383step0 raw15383step0Labels := by
      have hz : ∀ j, raw15383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15383step0 = (fun i j => raw15383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15383step0 raw15383; decide +kernel
      have hl : raw15383step0Labels = raw15383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15383 raw15383Labels permutation346 hz
    mixedMoment B raw15383step0 raw15383step0Labels = mixedMoment B raw15383step1 raw15383step1Labels := by
      have ha : raw15383step1 = (fun i j => raw15383step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15383step1 raw15383step0; decide +kernel
      have hl : raw15383step1Labels = raw15383step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15383step0 raw15383step0Labels permutation62 permutation5
    mixedMoment B raw15383step1 raw15383step1Labels = mixedMoment B raw15383step2 raw15383step2Labels := by
      have ha : raw15383step2 = -raw15383step1 := by apply Matrix.ext; change ∀ i j, raw15383step2 i j = -(raw15383step1 i j); unfold raw15383step2 raw15383step1; decide +kernel
      have hl : raw15383step2Labels = raw15383step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15383step2 raw15383step2Labels = mixedMoment B raw15383step3 raw15383step3Labels := by
      have ha : raw15383step3 = raw15383step2 := by apply Matrix.ext; unfold raw15383step3 raw15383step2; decide +kernel
      have hl : raw15383step2Labels = labelEmbedding8 ∘ raw15383step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15383step2 raw15383step2Labels raw15383step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw15384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15384step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15384 raw15384Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw15384 raw15384Labels = mixedMoment B raw15384step0 raw15384step0Labels := by
      have ha : raw15384step0 = (fun i j => raw15384 (permutation665 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15384step0 raw15384; decide +kernel
      have hl : raw15384step0Labels = raw15384Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15384 raw15384Labels permutation665 permutation5
    mixedMoment B raw15384step0 raw15384step0Labels = mixedMoment B raw15384step1 raw15384step1Labels := by
      have ha : raw15384step1 = raw15384step0 := by apply Matrix.ext; unfold raw15384step1 raw15384step0; decide +kernel
      have hl : raw15384step0Labels = labelEmbedding8 ∘ raw15384step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15384step0 raw15384step0Labels raw15384step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw15385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15385step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15385step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15385step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15385step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15385 raw15385Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw15385 raw15385Labels = mixedMoment B raw15385step0 raw15385step0Labels := by
      have hz : ∀ j, raw15385 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15385step0 = (fun i j => raw15385 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15385step0 raw15385; decide +kernel
      have hl : raw15385step0Labels = raw15385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15385 raw15385Labels permutation346 hz
    mixedMoment B raw15385step0 raw15385step0Labels = mixedMoment B raw15385step1 raw15385step1Labels := by
      have ha : raw15385step1 = (fun i j => raw15385step0 (permutation88 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15385step1 raw15385step0; decide +kernel
      have hl : raw15385step1Labels = raw15385step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15385step0 raw15385step0Labels permutation88 permutation4
    mixedMoment B raw15385step1 raw15385step1Labels = mixedMoment B raw15385step2 raw15385step2Labels := by
      have ha : raw15385step2 = -raw15385step1 := by apply Matrix.ext; change ∀ i j, raw15385step2 i j = -(raw15385step1 i j); unfold raw15385step2 raw15385step1; decide +kernel
      have hl : raw15385step2Labels = raw15385step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15385step2 raw15385step2Labels = mixedMoment B raw15385step3 raw15385step3Labels := by
      have ha : raw15385step3 = raw15385step2 := by apply Matrix.ext; unfold raw15385step3 raw15385step2; decide +kernel
      have hl : raw15385step2Labels = labelEmbedding7 ∘ raw15385step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15385step2 raw15385step2Labels raw15385step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw15386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw15386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw15386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw15386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15386step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15386step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15386step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15386step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15386step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15386 raw15386Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw15386 raw15386Labels = mixedMoment B raw15386step0 raw15386step0Labels := by
      have hz : ∀ j, raw15386 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15386step0 = (fun i j => raw15386 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15386step0 raw15386; decide +kernel
      have hl : raw15386step0Labels = raw15386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15386 raw15386Labels permutation520 hz
    mixedMoment B raw15386step0 raw15386step0Labels = mixedMoment B raw15386step1 raw15386step1Labels := by
      have hz : ∀ j, raw15386step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15386step1 = (fun i j => raw15386step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15386step1 raw15386step0; decide +kernel
      have hl : raw15386step1Labels = raw15386step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15386step0 raw15386step0Labels permutation80 hz
    mixedMoment B raw15386step1 raw15386step1Labels = mixedMoment B raw15386step2 raw15386step2Labels := by
      have ha : raw15386step2 = (fun i j => raw15386step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15386step2 raw15386step1; decide +kernel
      have hl : raw15386step2Labels = raw15386step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15386step1 raw15386step1Labels permutation22 permutation4
    mixedMoment B raw15386step2 raw15386step2Labels = mixedMoment B raw15386step3 raw15386step3Labels := by
      have ha : raw15386step3 = -raw15386step2 := by apply Matrix.ext; change ∀ i j, raw15386step3 i j = -(raw15386step2 i j); unfold raw15386step3 raw15386step2; decide +kernel
      have hl : raw15386step3Labels = raw15386step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15386step3 raw15386step3Labels = mixedMoment B raw15386step4 raw15386step4Labels := by
      have ha : raw15386step4 = raw15386step3 := by apply Matrix.ext; unfold raw15386step4 raw15386step3; decide +kernel
      have hl : raw15386step3Labels = labelEmbedding7 ∘ raw15386step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15386step3 raw15386step3Labels raw15386step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw15387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw15387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw15387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15387step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15387step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15387step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15387step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15387step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15387 raw15387Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw15387 raw15387Labels = mixedMoment B raw15387step0 raw15387step0Labels := by
      have hz : ∀ j, raw15387 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15387step0 = (fun i j => raw15387 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15387step0 raw15387; decide +kernel
      have hl : raw15387step0Labels = raw15387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15387 raw15387Labels permutation346 hz
    mixedMoment B raw15387step0 raw15387step0Labels = mixedMoment B raw15387step1 raw15387step1Labels := by
      have ha : raw15387step1 = (fun i j => raw15387step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15387step1 raw15387step0; decide +kernel
      have hl : raw15387step1Labels = raw15387step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15387step0 raw15387step0Labels permutation89 permutation4
    mixedMoment B raw15387step1 raw15387step1Labels = mixedMoment B raw15387step2 raw15387step2Labels := by
      have ha : raw15387step2 = -raw15387step1 := by apply Matrix.ext; change ∀ i j, raw15387step2 i j = -(raw15387step1 i j); unfold raw15387step2 raw15387step1; decide +kernel
      have hl : raw15387step2Labels = raw15387step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15387step2 raw15387step2Labels = mixedMoment B raw15387step3 raw15387step3Labels := by
      have ha : raw15387step3 = raw15387step2 := by apply Matrix.ext; unfold raw15387step3 raw15387step2; decide +kernel
      have hl : raw15387step2Labels = labelEmbedding7 ∘ raw15387step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15387step2 raw15387step2Labels raw15387step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw15388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15388 raw15388Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw15388 raw15388Labels = mixedMoment B raw15388step0 raw15388step0Labels := by
      have hz : ∀ j, raw15388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15388step0 = (fun i j => raw15388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15388step0 raw15388; decide +kernel
      have hl : raw15388step0Labels = raw15388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15388 raw15388Labels permutation346 hz
    mixedMoment B raw15388step0 raw15388step0Labels = mixedMoment B raw15388step1 raw15388step1Labels := by
      have hz : ∀ j, raw15388step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw15388step1 = (fun i j => raw15388step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw15388step1 raw15388step0; decide +kernel
      have hl : raw15388step1Labels = raw15388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15388step0 raw15388step0Labels permutation56 hz
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw15389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15389step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15389 raw15389Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw15389 raw15389Labels = mixedMoment B raw15389step0 raw15389step0Labels := by
      have ha : raw15389step0 = (fun i j => raw15389 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15389step0 raw15389; decide +kernel
      have hl : raw15389step0Labels = raw15389Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15389 raw15389Labels permutation271 permutation3
    mixedMoment B raw15389step0 raw15389step0Labels = mixedMoment B raw15389step1 raw15389step1Labels := by
      have ha : raw15389step1 = raw15389step0 := by apply Matrix.ext; unfold raw15389step1 raw15389step0; decide +kernel
      have hl : raw15389step0Labels = labelEmbedding6 ∘ raw15389step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15389step0 raw15389step0Labels raw15389step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw15390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw15390step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw15390step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15390step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw15390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15390 raw15390Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw15390 raw15390Labels = mixedMoment B raw15390step0 raw15390step0Labels := by
      have ha : raw15390step0 = (fun i j => raw15390 (permutation451 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15390step0 raw15390; decide +kernel
      have hl : raw15390step0Labels = raw15390Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15390 raw15390Labels permutation451 permutation4
    mixedMoment B raw15390step0 raw15390step0Labels = mixedMoment B raw15390step1 raw15390step1Labels := by
      have ha : raw15390step1 = -raw15390step0 := by apply Matrix.ext; change ∀ i j, raw15390step1 i j = -(raw15390step0 i j); unfold raw15390step1 raw15390step0; decide +kernel
      have hl : raw15390step1Labels = raw15390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15390step1 raw15390step1Labels = mixedMoment B raw15390step2 raw15390step2Labels := by
      have ha : raw15390step2 = raw15390step1 := by apply Matrix.ext; unfold raw15390step2 raw15390step1; decide +kernel
      have hl : raw15390step1Labels = labelEmbedding7 ∘ raw15390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15390step1 raw15390step1Labels raw15390step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw15391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw15391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw15391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15391step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15391step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15391step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15391step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15391 raw15391Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw15391 raw15391Labels = mixedMoment B raw15391step0 raw15391step0Labels := by
      have hz : ∀ j, raw15391 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15391step0 = (fun i j => raw15391 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15391step0 raw15391; decide +kernel
      have hl : raw15391step0Labels = raw15391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15391 raw15391Labels permutation520 hz
    mixedMoment B raw15391step0 raw15391step0Labels = mixedMoment B raw15391step1 raw15391step1Labels := by
      have ha : raw15391step1 = (fun i j => raw15391step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15391step1 raw15391step0; decide +kernel
      have hl : raw15391step1Labels = raw15391step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15391step0 raw15391step0Labels permutation145 permutation3
    mixedMoment B raw15391step1 raw15391step1Labels = mixedMoment B raw15391step2 raw15391step2Labels := by
      have ha : raw15391step2 = -raw15391step1 := by apply Matrix.ext; change ∀ i j, raw15391step2 i j = -(raw15391step1 i j); unfold raw15391step2 raw15391step1; decide +kernel
      have hl : raw15391step2Labels = raw15391step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15391step2 raw15391step2Labels = mixedMoment B raw15391step3 raw15391step3Labels := by
      have ha : raw15391step3 = raw15391step2 := by apply Matrix.ext; unfold raw15391step3 raw15391step2; decide +kernel
      have hl : raw15391step2Labels = labelEmbedding6 ∘ raw15391step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15391step2 raw15391step2Labels raw15391step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw15392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw15392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15392 raw15392Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw15392 raw15392Labels = mixedMoment B raw15392step0 raw15392step0Labels := by
      have ha : raw15392step0 = (fun i j => raw15392 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15392step0 raw15392; decide +kernel
      have hl : raw15392step0Labels = raw15392Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15392 raw15392Labels permutation158 permutation2
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw15393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15393step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15393 raw15393Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw15393 raw15393Labels = mixedMoment B raw15393step0 raw15393step0Labels := by
      have hz : ∀ j, raw15393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15393step0 = (fun i j => raw15393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15393step0 raw15393; decide +kernel
      have hl : raw15393step0Labels = raw15393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15393 raw15393Labels permutation346 hz
    mixedMoment B raw15393step0 raw15393step0Labels = mixedMoment B raw15393step1 raw15393step1Labels := by
      have ha : raw15393step1 = (fun i j => raw15393step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15393step1 raw15393step0; decide +kernel
      have hl : raw15393step1Labels = raw15393step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15393step0 raw15393step0Labels permutation56 permutation3
    mixedMoment B raw15393step1 raw15393step1Labels = mixedMoment B raw15393step2 raw15393step2Labels := by
      have ha : raw15393step2 = raw15393step1 := by apply Matrix.ext; unfold raw15393step2 raw15393step1; decide +kernel
      have hl : raw15393step1Labels = labelEmbedding6 ∘ raw15393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15393step1 raw15393step1Labels raw15393step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw15394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15394step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15394step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15394step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15394step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15394 raw15394Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw15394 raw15394Labels = mixedMoment B raw15394step0 raw15394step0Labels := by
      have ha : raw15394step0 = (fun i j => raw15394 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15394step0 raw15394; decide +kernel
      have hl : raw15394step0Labels = raw15394Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15394 raw15394Labels permutation686 permutation3
    mixedMoment B raw15394step0 raw15394step0Labels = mixedMoment B raw15394step1 raw15394step1Labels := by
      have ha : raw15394step1 = -raw15394step0 := by apply Matrix.ext; change ∀ i j, raw15394step1 i j = -(raw15394step0 i j); unfold raw15394step1 raw15394step0; decide +kernel
      have hl : raw15394step1Labels = raw15394step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15394step1 raw15394step1Labels = mixedMoment B raw15394step2 raw15394step2Labels := by
      have ha : raw15394step2 = raw15394step1 := by apply Matrix.ext; unfold raw15394step2 raw15394step1; decide +kernel
      have hl : raw15394step1Labels = labelEmbedding6 ∘ raw15394step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15394step1 raw15394step1Labels raw15394step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw15395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw15395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15395 raw15395Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw15395 raw15395Labels = mixedMoment B raw15395step0 raw15395step0Labels := by
      have hz : ∀ j, raw15395 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15395step0 = (fun i j => raw15395 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15395step0 raw15395; decide +kernel
      have hl : raw15395step0Labels = raw15395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15395 raw15395Labels permutation520 hz
    mixedMoment B raw15395step0 raw15395step0Labels = mixedMoment B raw15395step1 raw15395step1Labels := by
      have hz : ∀ j, raw15395step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15395step1 = (fun i j => raw15395step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15395step1 raw15395step0; decide +kernel
      have hl : raw15395step1Labels = raw15395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15395step0 raw15395step0Labels permutation80 hz
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw15396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw15396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw15396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15396 raw15396Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw15396 raw15396Labels = mixedMoment B raw15396step0 raw15396step0Labels := by
      have hz : ∀ j, raw15396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15396step0 = (fun i j => raw15396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15396step0 raw15396; decide +kernel
      have hl : raw15396step0Labels = raw15396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15396 raw15396Labels permutation346 hz
    mixedMoment B raw15396step0 raw15396step0Labels = mixedMoment B raw15396step1 raw15396step1Labels := by
      have ha : raw15396step1 = (fun i j => raw15396step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15396step1 raw15396step0; decide +kernel
      have hl : raw15396step1Labels = raw15396step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15396step0 raw15396step0Labels permutation35 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw15397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw15397step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15397step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15397step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15397step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15397 raw15397Labels = mixedMoment B node5329 node5329Labels := by
  calc
    mixedMoment B raw15397 raw15397Labels = mixedMoment B raw15397step0 raw15397step0Labels := by
      have hz : ∀ j, raw15397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15397step0 = (fun i j => raw15397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15397step0 raw15397; decide +kernel
      have hl : raw15397step0Labels = raw15397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15397 raw15397Labels permutation346 hz
    mixedMoment B raw15397step0 raw15397step0Labels = mixedMoment B raw15397step1 raw15397step1Labels := by
      have ha : raw15397step1 = (fun i j => raw15397step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15397step1 raw15397step0; decide +kernel
      have hl : raw15397step1Labels = raw15397step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15397step0 raw15397step0Labels permutation126 permutation3
    mixedMoment B raw15397step1 raw15397step1Labels = mixedMoment B raw15397step2 raw15397step2Labels := by
      have ha : raw15397step2 = -raw15397step1 := by apply Matrix.ext; change ∀ i j, raw15397step2 i j = -(raw15397step1 i j); unfold raw15397step2 raw15397step1; decide +kernel
      have hl : raw15397step2Labels = raw15397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15397step2 raw15397step2Labels = mixedMoment B raw15397step3 raw15397step3Labels := by
      have ha : raw15397step3 = raw15397step2 := by apply Matrix.ext; unfold raw15397step3 raw15397step2; decide +kernel
      have hl : raw15397step2Labels = labelEmbedding6 ∘ raw15397step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15397step2 raw15397step2Labels raw15397step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5329 node5329Labels := by rfl

def raw15398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15398step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15398 raw15398Labels = mixedMoment B node5328 node5328Labels := by
  calc
    mixedMoment B raw15398 raw15398Labels = mixedMoment B raw15398step0 raw15398step0Labels := by
      have ha : raw15398step0 = (fun i j => raw15398 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15398step0 raw15398; decide +kernel
      have hl : raw15398step0Labels = raw15398Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15398 raw15398Labels permutation587 permutation3
    mixedMoment B raw15398step0 raw15398step0Labels = mixedMoment B raw15398step1 raw15398step1Labels := by
      have ha : raw15398step1 = -raw15398step0 := by apply Matrix.ext; change ∀ i j, raw15398step1 i j = -(raw15398step0 i j); unfold raw15398step1 raw15398step0; decide +kernel
      have hl : raw15398step1Labels = raw15398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15398step1 raw15398step1Labels = mixedMoment B raw15398step2 raw15398step2Labels := by
      have ha : raw15398step2 = raw15398step1 := by apply Matrix.ext; unfold raw15398step2 raw15398step1; decide +kernel
      have hl : raw15398step1Labels = labelEmbedding6 ∘ raw15398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15398step1 raw15398step1Labels raw15398step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5328 node5328Labels := by rfl

def raw15399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw15399step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15399step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15399step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw15399step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15399 raw15399Labels = mixedMoment B node5156 node5156Labels := by
  calc
    mixedMoment B raw15399 raw15399Labels = mixedMoment B raw15399step0 raw15399step0Labels := by
      have hz : ∀ j, raw15399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15399step0 = (fun i j => raw15399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15399step0 raw15399; decide +kernel
      have hl : raw15399step0Labels = raw15399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15399 raw15399Labels permutation346 hz
    mixedMoment B raw15399step0 raw15399step0Labels = mixedMoment B raw15399step1 raw15399step1Labels := by
      have ha : raw15399step1 = (fun i j => raw15399step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15399step1 raw15399step0; decide +kernel
      have hl : raw15399step1Labels = raw15399step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15399step0 raw15399step0Labels permutation86 permutation4
    mixedMoment B raw15399step1 raw15399step1Labels = mixedMoment B raw15399step2 raw15399step2Labels := by
      have ha : raw15399step2 = -raw15399step1 := by apply Matrix.ext; change ∀ i j, raw15399step2 i j = -(raw15399step1 i j); unfold raw15399step2 raw15399step1; decide +kernel
      have hl : raw15399step2Labels = raw15399step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15399step2 raw15399step2Labels = mixedMoment B raw15399step3 raw15399step3Labels := by
      have ha : raw15399step3 = raw15399step2 := by apply Matrix.ext; unfold raw15399step3 raw15399step2; decide +kernel
      have hl : raw15399step2Labels = labelEmbedding7 ∘ raw15399step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15399step2 raw15399step2Labels raw15399step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5156 node5156Labels := by rfl

def raw15400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw15400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw15400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15400step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15400step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15400step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15400 raw15400Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw15400 raw15400Labels = mixedMoment B raw15400step0 raw15400step0Labels := by
      have hz : ∀ j, raw15400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15400step0 = (fun i j => raw15400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15400step0 raw15400; decide +kernel
      have hl : raw15400step0Labels = raw15400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15400 raw15400Labels permutation346 hz
    mixedMoment B raw15400step0 raw15400step0Labels = mixedMoment B raw15400step1 raw15400step1Labels := by
      have ha : raw15400step1 = (fun i j => raw15400step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15400step1 raw15400step0; decide +kernel
      have hl : raw15400step1Labels = raw15400step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15400step0 raw15400step0Labels permutation127 permutation3
    mixedMoment B raw15400step1 raw15400step1Labels = mixedMoment B raw15400step2 raw15400step2Labels := by
      have ha : raw15400step2 = -raw15400step1 := by apply Matrix.ext; change ∀ i j, raw15400step2 i j = -(raw15400step1 i j); unfold raw15400step2 raw15400step1; decide +kernel
      have hl : raw15400step2Labels = raw15400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15400step2 raw15400step2Labels = mixedMoment B raw15400step3 raw15400step3Labels := by
      have ha : raw15400step3 = raw15400step2 := by apply Matrix.ext; unfold raw15400step3 raw15400step2; decide +kernel
      have hl : raw15400step2Labels = labelEmbedding6 ∘ raw15400step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15400step2 raw15400step2Labels raw15400step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw15401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw15401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw15401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw15401step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15401step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15401step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15401step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15401 raw15401Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw15401 raw15401Labels = mixedMoment B raw15401step0 raw15401step0Labels := by
      have hz : ∀ j, raw15401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15401step0 = (fun i j => raw15401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15401step0 raw15401; decide +kernel
      have hl : raw15401step0Labels = raw15401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15401 raw15401Labels permutation346 hz
    mixedMoment B raw15401step0 raw15401step0Labels = mixedMoment B raw15401step1 raw15401step1Labels := by
      have ha : raw15401step1 = (fun i j => raw15401step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15401step1 raw15401step0; decide +kernel
      have hl : raw15401step1Labels = raw15401step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15401step0 raw15401step0Labels permutation150 permutation3
    mixedMoment B raw15401step1 raw15401step1Labels = mixedMoment B raw15401step2 raw15401step2Labels := by
      have ha : raw15401step2 = -raw15401step1 := by apply Matrix.ext; change ∀ i j, raw15401step2 i j = -(raw15401step1 i j); unfold raw15401step2 raw15401step1; decide +kernel
      have hl : raw15401step2Labels = raw15401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15401step2 raw15401step2Labels = mixedMoment B raw15401step3 raw15401step3Labels := by
      have ha : raw15401step3 = raw15401step2 := by apply Matrix.ext; unfold raw15401step3 raw15401step2; decide +kernel
      have hl : raw15401step2Labels = labelEmbedding6 ∘ raw15401step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15401step2 raw15401step2Labels raw15401step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

def raw15402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw15402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15402step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15402step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15402step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15402 raw15402Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw15402 raw15402Labels = mixedMoment B raw15402step0 raw15402step0Labels := by
      have ha : raw15402step0 = (fun i j => raw15402 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15402step0 raw15402; decide +kernel
      have hl : raw15402step0Labels = raw15402Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15402 raw15402Labels permutation686 permutation3
    mixedMoment B raw15402step0 raw15402step0Labels = mixedMoment B raw15402step1 raw15402step1Labels := by
      have ha : raw15402step1 = -raw15402step0 := by apply Matrix.ext; change ∀ i j, raw15402step1 i j = -(raw15402step0 i j); unfold raw15402step1 raw15402step0; decide +kernel
      have hl : raw15402step1Labels = raw15402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15402step1 raw15402step1Labels = mixedMoment B raw15402step2 raw15402step2Labels := by
      have ha : raw15402step2 = raw15402step1 := by apply Matrix.ext; unfold raw15402step2 raw15402step1; decide +kernel
      have hl : raw15402step1Labels = labelEmbedding6 ∘ raw15402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15402step1 raw15402step1Labels raw15402step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

def raw15403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw15403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw15403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw15403step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw15403step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15403 raw15403Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw15403 raw15403Labels = mixedMoment B raw15403step0 raw15403step0Labels := by
      have hz : ∀ j, raw15403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15403step0 = (fun i j => raw15403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15403step0 raw15403; decide +kernel
      have hl : raw15403step0Labels = raw15403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15403 raw15403Labels permutation346 hz
    mixedMoment B raw15403step0 raw15403step0Labels = mixedMoment B raw15403step1 raw15403step1Labels := by
      have ha : raw15403step1 = (fun i j => raw15403step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15403step1 raw15403step0; decide +kernel
      have hl : raw15403step1Labels = raw15403step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15403step0 raw15403step0Labels permutation146 permutation5
    mixedMoment B raw15403step1 raw15403step1Labels = mixedMoment B raw15403step2 raw15403step2Labels := by
      have ha : raw15403step2 = raw15403step1 := by apply Matrix.ext; unfold raw15403step2 raw15403step1; decide +kernel
      have hl : raw15403step1Labels = labelEmbedding8 ∘ raw15403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15403step1 raw15403step1Labels raw15403step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw15404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw15404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw15404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw15404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15404step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15404step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15404step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15404step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15404 raw15404Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw15404 raw15404Labels = mixedMoment B raw15404step0 raw15404step0Labels := by
      have hz : ∀ j, raw15404 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15404step0 = (fun i j => raw15404 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15404step0 raw15404; decide +kernel
      have hl : raw15404step0Labels = raw15404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15404 raw15404Labels permutation520 hz
    mixedMoment B raw15404step0 raw15404step0Labels = mixedMoment B raw15404step1 raw15404step1Labels := by
      have hz : ∀ j, raw15404step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15404step1 = (fun i j => raw15404step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15404step1 raw15404step0; decide +kernel
      have hl : raw15404step1Labels = raw15404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15404step0 raw15404step0Labels permutation80 hz
    mixedMoment B raw15404step1 raw15404step1Labels = mixedMoment B raw15404step2 raw15404step2Labels := by
      have ha : raw15404step2 = (fun i j => raw15404step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15404step2 raw15404step1; decide +kernel
      have hl : raw15404step2Labels = raw15404step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15404step1 raw15404step1Labels permutation31 permutation3
    mixedMoment B raw15404step2 raw15404step2Labels = mixedMoment B raw15404step3 raw15404step3Labels := by
      have ha : raw15404step3 = -raw15404step2 := by apply Matrix.ext; change ∀ i j, raw15404step3 i j = -(raw15404step2 i j); unfold raw15404step3 raw15404step2; decide +kernel
      have hl : raw15404step3Labels = raw15404step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15404step3 raw15404step3Labels = mixedMoment B raw15404step4 raw15404step4Labels := by
      have ha : raw15404step4 = raw15404step3 := by apply Matrix.ext; unfold raw15404step4 raw15404step3; decide +kernel
      have hl : raw15404step3Labels = labelEmbedding6 ∘ raw15404step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15404step3 raw15404step3Labels raw15404step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw15405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15405step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15405step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15405 raw15405Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15405 raw15405Labels = mixedMoment B raw15405step0 raw15405step0Labels := by
      have hz : ∀ j, raw15405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15405step0 = (fun i j => raw15405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15405step0 raw15405; decide +kernel
      have hl : raw15405step0Labels = raw15405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15405 raw15405Labels permutation346 hz
    mixedMoment B raw15405step0 raw15405step0Labels = mixedMoment B raw15405step1 raw15405step1Labels := by
      have ha : raw15405step1 = (fun i j => raw15405step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15405step1 raw15405step0; decide +kernel
      have hl : raw15405step1Labels = raw15405step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15405step0 raw15405step0Labels permutation146 permutation7
    mixedMoment B raw15405step1 raw15405step1Labels = mixedMoment B raw15405step2 raw15405step2Labels := by
      have ha : raw15405step2 = raw15405step1 := by apply Matrix.ext; unfold raw15405step2 raw15405step1; decide +kernel
      have hl : raw15405step1Labels = labelEmbedding10 ∘ raw15405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15405step1 raw15405step1Labels raw15405step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw15406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15406step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15406 raw15406Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw15406 raw15406Labels = mixedMoment B raw15406step0 raw15406step0Labels := by
      have ha : raw15406step0 = (fun i j => raw15406 (permutation667 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15406step0 raw15406; decide +kernel
      have hl : raw15406step0Labels = raw15406Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15406 raw15406Labels permutation667 permutation7
    mixedMoment B raw15406step0 raw15406step0Labels = mixedMoment B raw15406step1 raw15406step1Labels := by
      have ha : raw15406step1 = raw15406step0 := by apply Matrix.ext; unfold raw15406step1 raw15406step0; decide +kernel
      have hl : raw15406step0Labels = labelEmbedding10 ∘ raw15406step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15406step0 raw15406step0Labels raw15406step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw15407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15407step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15407step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15407step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15407 raw15407Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw15407 raw15407Labels = mixedMoment B raw15407step0 raw15407step0Labels := by
      have hz : ∀ j, raw15407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15407step0 = (fun i j => raw15407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15407step0 raw15407; decide +kernel
      have hl : raw15407step0Labels = raw15407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15407 raw15407Labels permutation346 hz
    mixedMoment B raw15407step0 raw15407step0Labels = mixedMoment B raw15407step1 raw15407step1Labels := by
      have ha : raw15407step1 = (fun i j => raw15407step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15407step1 raw15407step0; decide +kernel
      have hl : raw15407step1Labels = raw15407step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15407step0 raw15407step0Labels permutation146 permutation7
    mixedMoment B raw15407step1 raw15407step1Labels = mixedMoment B raw15407step2 raw15407step2Labels := by
      have ha : raw15407step2 = raw15407step1 := by apply Matrix.ext; unfold raw15407step2 raw15407step1; decide +kernel
      have hl : raw15407step1Labels = labelEmbedding10 ∘ raw15407step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15407step1 raw15407step1Labels raw15407step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw15408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15408step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15408step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15408step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15408step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15408step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15408 raw15408Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw15408 raw15408Labels = mixedMoment B raw15408step0 raw15408step0Labels := by
      have hz : ∀ j, raw15408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15408step0 = (fun i j => raw15408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15408step0 raw15408; decide +kernel
      have hl : raw15408step0Labels = raw15408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15408 raw15408Labels permutation346 hz
    mixedMoment B raw15408step0 raw15408step0Labels = mixedMoment B raw15408step1 raw15408step1Labels := by
      have ha : raw15408step1 = (fun i j => raw15408step0 (permutation86 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15408step1 raw15408step0; decide +kernel
      have hl : raw15408step1Labels = raw15408step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15408step0 raw15408step0Labels permutation86 permutation6
    mixedMoment B raw15408step1 raw15408step1Labels = mixedMoment B raw15408step2 raw15408step2Labels := by
      have ha : raw15408step2 = -raw15408step1 := by apply Matrix.ext; change ∀ i j, raw15408step2 i j = -(raw15408step1 i j); unfold raw15408step2 raw15408step1; decide +kernel
      have hl : raw15408step2Labels = raw15408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15408step2 raw15408step2Labels = mixedMoment B raw15408step3 raw15408step3Labels := by
      have ha : raw15408step3 = raw15408step2 := by apply Matrix.ext; unfold raw15408step3 raw15408step2; decide +kernel
      have hl : raw15408step2Labels = labelEmbedding9 ∘ raw15408step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15408step2 raw15408step2Labels raw15408step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw15409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15409step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15409step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15409step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15409step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15409 raw15409Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15409 raw15409Labels = mixedMoment B raw15409step0 raw15409step0Labels := by
      have hz : ∀ j, raw15409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15409step0 = (fun i j => raw15409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15409step0 raw15409; decide +kernel
      have hl : raw15409step0Labels = raw15409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15409 raw15409Labels permutation346 hz
    mixedMoment B raw15409step0 raw15409step0Labels = mixedMoment B raw15409step1 raw15409step1Labels := by
      have ha : raw15409step1 = (fun i j => raw15409step0 (permutation86 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15409step1 raw15409step0; decide +kernel
      have hl : raw15409step1Labels = raw15409step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15409step0 raw15409step0Labels permutation86 permutation6
    mixedMoment B raw15409step1 raw15409step1Labels = mixedMoment B raw15409step2 raw15409step2Labels := by
      have ha : raw15409step2 = -raw15409step1 := by apply Matrix.ext; change ∀ i j, raw15409step2 i j = -(raw15409step1 i j); unfold raw15409step2 raw15409step1; decide +kernel
      have hl : raw15409step2Labels = raw15409step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15409step2 raw15409step2Labels = mixedMoment B raw15409step3 raw15409step3Labels := by
      have ha : raw15409step3 = raw15409step2 := by apply Matrix.ext; unfold raw15409step3 raw15409step2; decide +kernel
      have hl : raw15409step2Labels = labelEmbedding9 ∘ raw15409step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15409step2 raw15409step2Labels raw15409step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw15410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15410step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15410step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15410 raw15410Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw15410 raw15410Labels = mixedMoment B raw15410step0 raw15410step0Labels := by
      have hz : ∀ j, raw15410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15410step0 = (fun i j => raw15410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15410step0 raw15410; decide +kernel
      have hl : raw15410step0Labels = raw15410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15410 raw15410Labels permutation346 hz
    mixedMoment B raw15410step0 raw15410step0Labels = mixedMoment B raw15410step1 raw15410step1Labels := by
      have ha : raw15410step1 = (fun i j => raw15410step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15410step1 raw15410step0; decide +kernel
      have hl : raw15410step1Labels = raw15410step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15410step0 raw15410step0Labels permutation32 permutation3
    mixedMoment B raw15410step1 raw15410step1Labels = mixedMoment B raw15410step2 raw15410step2Labels := by
      have ha : raw15410step2 = raw15410step1 := by apply Matrix.ext; unfold raw15410step2 raw15410step1; decide +kernel
      have hl : raw15410step1Labels = labelEmbedding6 ∘ raw15410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15410step1 raw15410step1Labels raw15410step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw15411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15411 raw15411Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw15411 raw15411Labels = mixedMoment B raw15411step0 raw15411step0Labels := by
      have ha : raw15411step0 = (fun i j => raw15411 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15411step0 raw15411; decide +kernel
      have hl : raw15411step0Labels = raw15411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15411 raw15411Labels permutation676 permutation2
    mixedMoment B raw15411step0 raw15411step0Labels = mixedMoment B raw15411step1 raw15411step1Labels := by
      have ha : raw15411step1 = -raw15411step0 := by apply Matrix.ext; change ∀ i j, raw15411step1 i j = -(raw15411step0 i j); unfold raw15411step1 raw15411step0; decide +kernel
      have hl : raw15411step1Labels = raw15411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5407 node5407Labels := by rfl

def raw15412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15412step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15412 raw15412Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15412 raw15412Labels = mixedMoment B raw15412step0 raw15412step0Labels := by
      have hz : ∀ j, raw15412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15412step0 = (fun i j => raw15412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15412step0 raw15412; decide +kernel
      have hl : raw15412step0Labels = raw15412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15412 raw15412Labels permutation346 hz
    mixedMoment B raw15412step0 raw15412step0Labels = mixedMoment B raw15412step1 raw15412step1Labels := by
      have ha : raw15412step1 = (fun i j => raw15412step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15412step1 raw15412step0; decide +kernel
      have hl : raw15412step1Labels = raw15412step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15412step0 raw15412step0Labels permutation149 permutation2
    mixedMoment B raw15412step1 raw15412step1Labels = mixedMoment B raw15412step2 raw15412step2Labels := by
      have ha : raw15412step2 = -raw15412step1 := by apply Matrix.ext; change ∀ i j, raw15412step2 i j = -(raw15412step1 i j); unfold raw15412step2 raw15412step1; decide +kernel
      have hl : raw15412step2Labels = raw15412step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw15413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15413step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15413step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15413 raw15413Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw15413 raw15413Labels = mixedMoment B raw15413step0 raw15413step0Labels := by
      have hz : ∀ j, raw15413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15413step0 = (fun i j => raw15413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15413step0 raw15413; decide +kernel
      have hl : raw15413step0Labels = raw15413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15413 raw15413Labels permutation346 hz
    mixedMoment B raw15413step0 raw15413step0Labels = mixedMoment B raw15413step1 raw15413step1Labels := by
      have ha : raw15413step1 = (fun i j => raw15413step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15413step1 raw15413step0; decide +kernel
      have hl : raw15413step1Labels = raw15413step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15413step0 raw15413step0Labels permutation91 permutation4
    mixedMoment B raw15413step1 raw15413step1Labels = mixedMoment B raw15413step2 raw15413step2Labels := by
      have ha : raw15413step2 = raw15413step1 := by apply Matrix.ext; unfold raw15413step2 raw15413step1; decide +kernel
      have hl : raw15413step1Labels = labelEmbedding7 ∘ raw15413step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15413step1 raw15413step1Labels raw15413step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw15414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15414step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15414step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15414 raw15414Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15414 raw15414Labels = mixedMoment B raw15414step0 raw15414step0Labels := by
      have hz : ∀ j, raw15414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15414step0 = (fun i j => raw15414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15414step0 raw15414; decide +kernel
      have hl : raw15414step0Labels = raw15414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15414 raw15414Labels permutation346 hz
    mixedMoment B raw15414step0 raw15414step0Labels = mixedMoment B raw15414step1 raw15414step1Labels := by
      have ha : raw15414step1 = (fun i j => raw15414step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15414step1 raw15414step0; decide +kernel
      have hl : raw15414step1Labels = raw15414step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15414step0 raw15414step0Labels permutation89 permutation4
    mixedMoment B raw15414step1 raw15414step1Labels = mixedMoment B raw15414step2 raw15414step2Labels := by
      have ha : raw15414step2 = raw15414step1 := by apply Matrix.ext; unfold raw15414step2 raw15414step1; decide +kernel
      have hl : raw15414step1Labels = labelEmbedding7 ∘ raw15414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15414step1 raw15414step1Labels raw15414step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw15415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15415step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15415 raw15415Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw15415 raw15415Labels = mixedMoment B raw15415step0 raw15415step0Labels := by
      have ha : raw15415step0 = (fun i j => raw15415 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15415step0 raw15415; decide +kernel
      have hl : raw15415step0Labels = raw15415Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15415 raw15415Labels permutation160 permutation3
    mixedMoment B raw15415step0 raw15415step0Labels = mixedMoment B raw15415step1 raw15415step1Labels := by
      have ha : raw15415step1 = raw15415step0 := by apply Matrix.ext; unfold raw15415step1 raw15415step0; decide +kernel
      have hl : raw15415step0Labels = labelEmbedding6 ∘ raw15415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15415step0 raw15415step0Labels raw15415step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw15416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15416step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15416 raw15416Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw15416 raw15416Labels = mixedMoment B raw15416step0 raw15416step0Labels := by
      have ha : raw15416step0 = (fun i j => raw15416 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15416step0 raw15416; decide +kernel
      have hl : raw15416step0Labels = raw15416Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15416 raw15416Labels permutation160 permutation3
    mixedMoment B raw15416step0 raw15416step0Labels = mixedMoment B raw15416step1 raw15416step1Labels := by
      have ha : raw15416step1 = raw15416step0 := by apply Matrix.ext; unfold raw15416step1 raw15416step0; decide +kernel
      have hl : raw15416step0Labels = labelEmbedding6 ∘ raw15416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15416step0 raw15416step0Labels raw15416step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw15417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15417 raw15417Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw15417 raw15417Labels = mixedMoment B raw15417step0 raw15417step0Labels := by
      have ha : raw15417step0 = (fun i j => raw15417 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15417step0 raw15417; decide +kernel
      have hl : raw15417step0Labels = raw15417Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15417 raw15417Labels permutation680 permutation2
    mixedMoment B raw15417step0 raw15417step0Labels = mixedMoment B raw15417step1 raw15417step1Labels := by
      have ha : raw15417step1 = -raw15417step0 := by apply Matrix.ext; change ∀ i j, raw15417step1 i j = -(raw15417step0 i j); unfold raw15417step1 raw15417step0; decide +kernel
      have hl : raw15417step1Labels = raw15417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw15418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15418 raw15418Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw15418 raw15418Labels = mixedMoment B raw15418step0 raw15418step0Labels := by
      have ha : raw15418step0 = (fun i j => raw15418 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15418step0 raw15418; decide +kernel
      have hl : raw15418step0Labels = raw15418Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15418 raw15418Labels permutation646 permutation2
    mixedMoment B raw15418step0 raw15418step0Labels = mixedMoment B raw15418step1 raw15418step1Labels := by
      have ha : raw15418step1 = -raw15418step0 := by apply Matrix.ext; change ∀ i j, raw15418step1 i j = -(raw15418step0 i j); unfold raw15418step1 raw15418step0; decide +kernel
      have hl : raw15418step1Labels = raw15418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5426 node5426Labels := by rfl

def raw15419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15419step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15419 raw15419Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw15419 raw15419Labels = mixedMoment B raw15419step0 raw15419step0Labels := by
      have ha : raw15419step0 = (fun i j => raw15419 (permutation473 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15419step0 raw15419; decide +kernel
      have hl : raw15419step0Labels = raw15419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15419 raw15419Labels permutation473 permutation4
    mixedMoment B raw15419step0 raw15419step0Labels = mixedMoment B raw15419step1 raw15419step1Labels := by
      have ha : raw15419step1 = raw15419step0 := by apply Matrix.ext; unfold raw15419step1 raw15419step0; decide +kernel
      have hl : raw15419step0Labels = labelEmbedding7 ∘ raw15419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15419step0 raw15419step0Labels raw15419step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw15420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw15420step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw15420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15420 raw15420Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw15420 raw15420Labels = mixedMoment B raw15420step0 raw15420step0Labels := by
      have hz : ∀ j, raw15420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15420step0 = (fun i j => raw15420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15420step0 raw15420; decide +kernel
      have hl : raw15420step0Labels = raw15420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15420 raw15420Labels permutation346 hz
    mixedMoment B raw15420step0 raw15420step0Labels = mixedMoment B raw15420step1 raw15420step1Labels := by
      have ha : raw15420step1 = (fun i j => raw15420step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15420step1 raw15420step0; decide +kernel
      have hl : raw15420step1Labels = raw15420step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15420step0 raw15420step0Labels permutation34 permutation3
    mixedMoment B raw15420step1 raw15420step1Labels = mixedMoment B raw15420step2 raw15420step2Labels := by
      have ha : raw15420step2 = raw15420step1 := by apply Matrix.ext; unfold raw15420step2 raw15420step1; decide +kernel
      have hl : raw15420step1Labels = labelEmbedding6 ∘ raw15420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15420step1 raw15420step1Labels raw15420step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw15421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw15421step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw15421step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15421 raw15421Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw15421 raw15421Labels = mixedMoment B raw15421step0 raw15421step0Labels := by
      have hz : ∀ j, raw15421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15421step0 = (fun i j => raw15421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15421step0 raw15421; decide +kernel
      have hl : raw15421step0Labels = raw15421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15421 raw15421Labels permutation346 hz
    mixedMoment B raw15421step0 raw15421step0Labels = mixedMoment B raw15421step1 raw15421step1Labels := by
      have ha : raw15421step1 = (fun i j => raw15421step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15421step1 raw15421step0; decide +kernel
      have hl : raw15421step1Labels = raw15421step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15421step0 raw15421step0Labels permutation97 permutation4
    mixedMoment B raw15421step1 raw15421step1Labels = mixedMoment B raw15421step2 raw15421step2Labels := by
      have ha : raw15421step2 = raw15421step1 := by apply Matrix.ext; unfold raw15421step2 raw15421step1; decide +kernel
      have hl : raw15421step1Labels = labelEmbedding7 ∘ raw15421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15421step1 raw15421step1Labels raw15421step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw15422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15422step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15422 raw15422Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw15422 raw15422Labels = mixedMoment B raw15422step0 raw15422step0Labels := by
      have ha : raw15422step0 = (fun i j => raw15422 (permutation463 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15422step0 raw15422; decide +kernel
      have hl : raw15422step0Labels = raw15422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15422 raw15422Labels permutation463 permutation4
    mixedMoment B raw15422step0 raw15422step0Labels = mixedMoment B raw15422step1 raw15422step1Labels := by
      have ha : raw15422step1 = raw15422step0 := by apply Matrix.ext; unfold raw15422step1 raw15422step0; decide +kernel
      have hl : raw15422step0Labels = labelEmbedding7 ∘ raw15422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15422step0 raw15422step0Labels raw15422step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw15423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15423step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15423step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15423 raw15423Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw15423 raw15423Labels = mixedMoment B raw15423step0 raw15423step0Labels := by
      have hz : ∀ j, raw15423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15423step0 = (fun i j => raw15423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15423step0 raw15423; decide +kernel
      have hl : raw15423step0Labels = raw15423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15423 raw15423Labels permutation346 hz
    mixedMoment B raw15423step0 raw15423step0Labels = mixedMoment B raw15423step1 raw15423step1Labels := by
      have ha : raw15423step1 = (fun i j => raw15423step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15423step1 raw15423step0; decide +kernel
      have hl : raw15423step1Labels = raw15423step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15423step0 raw15423step0Labels permutation91 permutation4
    mixedMoment B raw15423step1 raw15423step1Labels = mixedMoment B raw15423step2 raw15423step2Labels := by
      have ha : raw15423step2 = raw15423step1 := by apply Matrix.ext; unfold raw15423step2 raw15423step1; decide +kernel
      have hl : raw15423step1Labels = labelEmbedding7 ∘ raw15423step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15423step1 raw15423step1Labels raw15423step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw15424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15424step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15424step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15424 raw15424Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw15424 raw15424Labels = mixedMoment B raw15424step0 raw15424step0Labels := by
      have hz : ∀ j, raw15424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15424step0 = (fun i j => raw15424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15424step0 raw15424; decide +kernel
      have hl : raw15424step0Labels = raw15424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15424 raw15424Labels permutation346 hz
    mixedMoment B raw15424step0 raw15424step0Labels = mixedMoment B raw15424step1 raw15424step1Labels := by
      have ha : raw15424step1 = (fun i j => raw15424step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15424step1 raw15424step0; decide +kernel
      have hl : raw15424step1Labels = raw15424step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15424step0 raw15424step0Labels permutation89 permutation4
    mixedMoment B raw15424step1 raw15424step1Labels = mixedMoment B raw15424step2 raw15424step2Labels := by
      have ha : raw15424step2 = raw15424step1 := by apply Matrix.ext; unfold raw15424step2 raw15424step1; decide +kernel
      have hl : raw15424step1Labels = labelEmbedding7 ∘ raw15424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15424step1 raw15424step1Labels raw15424step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw15425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15425step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15425 raw15425Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw15425 raw15425Labels = mixedMoment B raw15425step0 raw15425step0Labels := by
      have hz : ∀ j, raw15425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15425step0 = (fun i j => raw15425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15425step0 raw15425; decide +kernel
      have hl : raw15425step0Labels = raw15425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15425 raw15425Labels permutation346 hz
    mixedMoment B raw15425step0 raw15425step0Labels = mixedMoment B raw15425step1 raw15425step1Labels := by
      have ha : raw15425step1 = (fun i j => raw15425step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15425step1 raw15425step0; decide +kernel
      have hl : raw15425step1Labels = raw15425step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15425step0 raw15425step0Labels permutation33 permutation3
    mixedMoment B raw15425step1 raw15425step1Labels = mixedMoment B raw15425step2 raw15425step2Labels := by
      have ha : raw15425step2 = raw15425step1 := by apply Matrix.ext; unfold raw15425step2 raw15425step1; decide +kernel
      have hl : raw15425step1Labels = labelEmbedding6 ∘ raw15425step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15425step1 raw15425step1Labels raw15425step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw15426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15426 raw15426Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw15426 raw15426Labels = mixedMoment B raw15426step0 raw15426step0Labels := by
      have hz : ∀ j, raw15426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15426step0 = (fun i j => raw15426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15426step0 raw15426; decide +kernel
      have hl : raw15426step0Labels = raw15426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15426 raw15426Labels permutation346 hz
    mixedMoment B raw15426step0 raw15426step0Labels = mixedMoment B raw15426step1 raw15426step1Labels := by
      have ha : raw15426step1 = (fun i j => raw15426step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15426step1 raw15426step0; decide +kernel
      have hl : raw15426step1Labels = raw15426step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15426step0 raw15426step0Labels permutation150 permutation2
    mixedMoment B raw15426step1 raw15426step1Labels = mixedMoment B raw15426step2 raw15426step2Labels := by
      have ha : raw15426step2 = -raw15426step1 := by apply Matrix.ext; change ∀ i j, raw15426step2 i j = -(raw15426step1 i j); unfold raw15426step2 raw15426step1; decide +kernel
      have hl : raw15426step2Labels = raw15426step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5361 node5361Labels := by rfl

def raw15427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15427 raw15427Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw15427 raw15427Labels = mixedMoment B raw15427step0 raw15427step0Labels := by
      have ha : raw15427step0 = (fun i j => raw15427 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15427step0 raw15427; decide +kernel
      have hl : raw15427step0Labels = raw15427Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15427 raw15427Labels permutation688 permutation2
    mixedMoment B raw15427step0 raw15427step0Labels = mixedMoment B raw15427step1 raw15427step1Labels := by
      have ha : raw15427step1 = -raw15427step0 := by apply Matrix.ext; change ∀ i j, raw15427step1 i j = -(raw15427step0 i j); unfold raw15427step1 raw15427step0; decide +kernel
      have hl : raw15427step1Labels = raw15427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw15428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15428 raw15428Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw15428 raw15428Labels = mixedMoment B raw15428step0 raw15428step0Labels := by
      have hz : ∀ j, raw15428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15428step0 = (fun i j => raw15428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15428step0 raw15428; decide +kernel
      have hl : raw15428step0Labels = raw15428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15428 raw15428Labels permutation346 hz
    mixedMoment B raw15428step0 raw15428step0Labels = mixedMoment B raw15428step1 raw15428step1Labels := by
      have ha : raw15428step1 = (fun i j => raw15428step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15428step1 raw15428step0; decide +kernel
      have hl : raw15428step1Labels = raw15428step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15428step0 raw15428step0Labels permutation149 permutation2
    mixedMoment B raw15428step1 raw15428step1Labels = mixedMoment B raw15428step2 raw15428step2Labels := by
      have ha : raw15428step2 = -raw15428step1 := by apply Matrix.ext; change ∀ i j, raw15428step2 i j = -(raw15428step1 i j); unfold raw15428step2 raw15428step1; decide +kernel
      have hl : raw15428step2Labels = raw15428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw15429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw15429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw15429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15429step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15429 raw15429Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw15429 raw15429Labels = mixedMoment B raw15429step0 raw15429step0Labels := by
      have hz : ∀ j, raw15429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15429step0 = (fun i j => raw15429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15429step0 raw15429; decide +kernel
      have hl : raw15429step0Labels = raw15429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15429 raw15429Labels permutation346 hz
    mixedMoment B raw15429step0 raw15429step0Labels = mixedMoment B raw15429step1 raw15429step1Labels := by
      have ha : raw15429step1 = (fun i j => raw15429step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15429step1 raw15429step0; decide +kernel
      have hl : raw15429step1Labels = raw15429step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15429step0 raw15429step0Labels permutation33 permutation3
    mixedMoment B raw15429step1 raw15429step1Labels = mixedMoment B raw15429step2 raw15429step2Labels := by
      have ha : raw15429step2 = raw15429step1 := by apply Matrix.ext; unfold raw15429step2 raw15429step1; decide +kernel
      have hl : raw15429step1Labels = labelEmbedding6 ∘ raw15429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15429step1 raw15429step1Labels raw15429step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw15430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw15430step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw15430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15430 raw15430Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw15430 raw15430Labels = mixedMoment B raw15430step0 raw15430step0Labels := by
      have hz : ∀ j, raw15430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15430step0 = (fun i j => raw15430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15430step0 raw15430; decide +kernel
      have hl : raw15430step0Labels = raw15430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15430 raw15430Labels permutation346 hz
    mixedMoment B raw15430step0 raw15430step0Labels = mixedMoment B raw15430step1 raw15430step1Labels := by
      have ha : raw15430step1 = (fun i j => raw15430step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15430step1 raw15430step0; decide +kernel
      have hl : raw15430step1Labels = raw15430step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15430step0 raw15430step0Labels permutation32 permutation3
    mixedMoment B raw15430step1 raw15430step1Labels = mixedMoment B raw15430step2 raw15430step2Labels := by
      have ha : raw15430step2 = raw15430step1 := by apply Matrix.ext; unfold raw15430step2 raw15430step1; decide +kernel
      have hl : raw15430step1Labels = labelEmbedding6 ∘ raw15430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15430step1 raw15430step1Labels raw15430step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw15431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15431step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15431 raw15431Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw15431 raw15431Labels = mixedMoment B raw15431step0 raw15431step0Labels := by
      have hz : ∀ j, raw15431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15431step0 = (fun i j => raw15431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15431step0 raw15431; decide +kernel
      have hl : raw15431step0Labels = raw15431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15431 raw15431Labels permutation346 hz
    mixedMoment B raw15431step0 raw15431step0Labels = mixedMoment B raw15431step1 raw15431step1Labels := by
      have ha : raw15431step1 = (fun i j => raw15431step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15431step1 raw15431step0; decide +kernel
      have hl : raw15431step1Labels = raw15431step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15431step0 raw15431step0Labels permutation150 permutation2
    mixedMoment B raw15431step1 raw15431step1Labels = mixedMoment B raw15431step2 raw15431step2Labels := by
      have ha : raw15431step2 = -raw15431step1 := by apply Matrix.ext; change ∀ i j, raw15431step2 i j = -(raw15431step1 i j); unfold raw15431step2 raw15431step1; decide +kernel
      have hl : raw15431step2Labels = raw15431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw15432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15432 raw15432Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw15432 raw15432Labels = mixedMoment B raw15432step0 raw15432step0Labels := by
      have ha : raw15432step0 = (fun i j => raw15432 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15432step0 raw15432; decide +kernel
      have hl : raw15432step0Labels = raw15432Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15432 raw15432Labels permutation688 permutation2
    mixedMoment B raw15432step0 raw15432step0Labels = mixedMoment B raw15432step1 raw15432step1Labels := by
      have ha : raw15432step1 = -raw15432step0 := by apply Matrix.ext; change ∀ i j, raw15432step1 i j = -(raw15432step0 i j); unfold raw15432step1 raw15432step0; decide +kernel
      have hl : raw15432step1Labels = raw15432step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw15433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15433step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15433step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15433 raw15433Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw15433 raw15433Labels = mixedMoment B raw15433step0 raw15433step0Labels := by
      have hz : ∀ j, raw15433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15433step0 = (fun i j => raw15433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15433step0 raw15433; decide +kernel
      have hl : raw15433step0Labels = raw15433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15433 raw15433Labels permutation346 hz
    mixedMoment B raw15433step0 raw15433step0Labels = mixedMoment B raw15433step1 raw15433step1Labels := by
      have ha : raw15433step1 = (fun i j => raw15433step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15433step1 raw15433step0; decide +kernel
      have hl : raw15433step1Labels = raw15433step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15433step0 raw15433step0Labels permutation149 permutation2
    mixedMoment B raw15433step1 raw15433step1Labels = mixedMoment B raw15433step2 raw15433step2Labels := by
      have ha : raw15433step2 = -raw15433step1 := by apply Matrix.ext; change ∀ i j, raw15433step2 i j = -(raw15433step1 i j); unfold raw15433step2 raw15433step1; decide +kernel
      have hl : raw15433step2Labels = raw15433step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw15434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw15434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw15434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15434step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15434 raw15434Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw15434 raw15434Labels = mixedMoment B raw15434step0 raw15434step0Labels := by
      have hz : ∀ j, raw15434 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15434step0 = (fun i j => raw15434 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15434step0 raw15434; decide +kernel
      have hl : raw15434step0Labels = raw15434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15434 raw15434Labels permutation346 hz
    mixedMoment B raw15434step0 raw15434step0Labels = mixedMoment B raw15434step1 raw15434step1Labels := by
      have ha : raw15434step1 = (fun i j => raw15434step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15434step1 raw15434step0; decide +kernel
      have hl : raw15434step1Labels = raw15434step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15434step0 raw15434step0Labels permutation151 permutation2
    mixedMoment B raw15434step1 raw15434step1Labels = mixedMoment B raw15434step2 raw15434step2Labels := by
      have ha : raw15434step2 = -raw15434step1 := by apply Matrix.ext; change ∀ i j, raw15434step2 i j = -(raw15434step1 i j); unfold raw15434step2 raw15434step1; decide +kernel
      have hl : raw15434step2Labels = raw15434step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw15435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15435 raw15435Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw15435 raw15435Labels = mixedMoment B raw15435step0 raw15435step0Labels := by
      have hz : ∀ j, raw15435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15435step0 = (fun i j => raw15435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15435step0 raw15435; decide +kernel
      have hl : raw15435step0Labels = raw15435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15435 raw15435Labels permutation346 hz
    mixedMoment B raw15435step0 raw15435step0Labels = mixedMoment B raw15435step1 raw15435step1Labels := by
      have ha : raw15435step1 = (fun i j => raw15435step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15435step1 raw15435step0; decide +kernel
      have hl : raw15435step1Labels = raw15435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15435step0 raw15435step0Labels permutation146 permutation7
    mixedMoment B raw15435step1 raw15435step1Labels = mixedMoment B raw15435step2 raw15435step2Labels := by
      have ha : raw15435step2 = raw15435step1 := by apply Matrix.ext; unfold raw15435step2 raw15435step1; decide +kernel
      have hl : raw15435step1Labels = labelEmbedding1 ∘ raw15435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15435step1 raw15435step1Labels raw15435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw15436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15436step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15436 raw15436Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw15436 raw15436Labels = mixedMoment B raw15436step0 raw15436step0Labels := by
      have ha : raw15436step0 = (fun i j => raw15436 (permutation667 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15436step0 raw15436; decide +kernel
      have hl : raw15436step0Labels = raw15436Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15436 raw15436Labels permutation667 permutation7
    mixedMoment B raw15436step0 raw15436step0Labels = mixedMoment B raw15436step1 raw15436step1Labels := by
      have ha : raw15436step1 = raw15436step0 := by apply Matrix.ext; unfold raw15436step1 raw15436step0; decide +kernel
      have hl : raw15436step0Labels = labelEmbedding1 ∘ raw15436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15436step0 raw15436step0Labels raw15436step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw15437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15437step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15437step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15437 raw15437Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw15437 raw15437Labels = mixedMoment B raw15437step0 raw15437step0Labels := by
      have hz : ∀ j, raw15437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15437step0 = (fun i j => raw15437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15437step0 raw15437; decide +kernel
      have hl : raw15437step0Labels = raw15437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15437 raw15437Labels permutation346 hz
    mixedMoment B raw15437step0 raw15437step0Labels = mixedMoment B raw15437step1 raw15437step1Labels := by
      have ha : raw15437step1 = (fun i j => raw15437step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15437step1 raw15437step0; decide +kernel
      have hl : raw15437step1Labels = raw15437step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15437step0 raw15437step0Labels permutation146 permutation7
    mixedMoment B raw15437step1 raw15437step1Labels = mixedMoment B raw15437step2 raw15437step2Labels := by
      have ha : raw15437step2 = raw15437step1 := by apply Matrix.ext; unfold raw15437step2 raw15437step1; decide +kernel
      have hl : raw15437step1Labels = labelEmbedding1 ∘ raw15437step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15437step1 raw15437step1Labels raw15437step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw15438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15438step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15438step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15438 raw15438Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw15438 raw15438Labels = mixedMoment B raw15438step0 raw15438step0Labels := by
      have hz : ∀ j, raw15438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15438step0 = (fun i j => raw15438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15438step0 raw15438; decide +kernel
      have hl : raw15438step0Labels = raw15438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15438 raw15438Labels permutation346 hz
    mixedMoment B raw15438step0 raw15438step0Labels = mixedMoment B raw15438step1 raw15438step1Labels := by
      have ha : raw15438step1 = (fun i j => raw15438step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15438step1 raw15438step0; decide +kernel
      have hl : raw15438step1Labels = raw15438step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15438step0 raw15438step0Labels permutation146 permutation7
    mixedMoment B raw15438step1 raw15438step1Labels = mixedMoment B raw15438step2 raw15438step2Labels := by
      have ha : raw15438step2 = raw15438step1 := by apply Matrix.ext; unfold raw15438step2 raw15438step1; decide +kernel
      have hl : raw15438step1Labels = labelEmbedding1 ∘ raw15438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15438step1 raw15438step1Labels raw15438step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw15439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15439 raw15439Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw15439 raw15439Labels = mixedMoment B raw15439step0 raw15439step0Labels := by
      have hz : ∀ j, raw15439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15439step0 = (fun i j => raw15439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15439step0 raw15439; decide +kernel
      have hl : raw15439step0Labels = raw15439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15439 raw15439Labels permutation346 hz
    mixedMoment B raw15439step0 raw15439step0Labels = mixedMoment B raw15439step1 raw15439step1Labels := by
      have ha : raw15439step1 = (fun i j => raw15439step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15439step1 raw15439step0; decide +kernel
      have hl : raw15439step1Labels = raw15439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15439step0 raw15439step0Labels permutation146 permutation7
    mixedMoment B raw15439step1 raw15439step1Labels = mixedMoment B raw15439step2 raw15439step2Labels := by
      have ha : raw15439step2 = raw15439step1 := by apply Matrix.ext; unfold raw15439step2 raw15439step1; decide +kernel
      have hl : raw15439step1Labels = labelEmbedding1 ∘ raw15439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15439step1 raw15439step1Labels raw15439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw15440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15440step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15440step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15440 raw15440Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw15440 raw15440Labels = mixedMoment B raw15440step0 raw15440step0Labels := by
      have hz : ∀ j, raw15440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15440step0 = (fun i j => raw15440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15440step0 raw15440; decide +kernel
      have hl : raw15440step0Labels = raw15440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15440 raw15440Labels permutation346 hz
    mixedMoment B raw15440step0 raw15440step0Labels = mixedMoment B raw15440step1 raw15440step1Labels := by
      have ha : raw15440step1 = (fun i j => raw15440step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15440step1 raw15440step0; decide +kernel
      have hl : raw15440step1Labels = raw15440step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15440step0 raw15440step0Labels permutation48 permutation5
    mixedMoment B raw15440step1 raw15440step1Labels = mixedMoment B raw15440step2 raw15440step2Labels := by
      have ha : raw15440step2 = -raw15440step1 := by apply Matrix.ext; change ∀ i j, raw15440step2 i j = -(raw15440step1 i j); unfold raw15440step2 raw15440step1; decide +kernel
      have hl : raw15440step2Labels = raw15440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15440step2 raw15440step2Labels = mixedMoment B raw15440step3 raw15440step3Labels := by
      have ha : raw15440step3 = raw15440step2 := by apply Matrix.ext; unfold raw15440step3 raw15440step2; decide +kernel
      have hl : raw15440step2Labels = labelEmbedding1 ∘ raw15440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15440step2 raw15440step2Labels raw15440step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw15441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15441step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15441step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15441 raw15441Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw15441 raw15441Labels = mixedMoment B raw15441step0 raw15441step0Labels := by
      have ha : raw15441step0 = (fun i j => raw15441 (permutation192 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15441step0 raw15441; decide +kernel
      have hl : raw15441step0Labels = raw15441Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15441 raw15441Labels permutation192 permutation5
    mixedMoment B raw15441step0 raw15441step0Labels = mixedMoment B raw15441step1 raw15441step1Labels := by
      have ha : raw15441step1 = -raw15441step0 := by apply Matrix.ext; change ∀ i j, raw15441step1 i j = -(raw15441step0 i j); unfold raw15441step1 raw15441step0; decide +kernel
      have hl : raw15441step1Labels = raw15441step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15441step1 raw15441step1Labels = mixedMoment B raw15441step2 raw15441step2Labels := by
      have ha : raw15441step2 = raw15441step1 := by apply Matrix.ext; unfold raw15441step2 raw15441step1; decide +kernel
      have hl : raw15441step1Labels = labelEmbedding1 ∘ raw15441step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15441step1 raw15441step1Labels raw15441step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw15442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15442step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15442 raw15442Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw15442 raw15442Labels = mixedMoment B raw15442step0 raw15442step0Labels := by
      have hz : ∀ j, raw15442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15442step0 = (fun i j => raw15442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15442step0 raw15442; decide +kernel
      have hl : raw15442step0Labels = raw15442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15442 raw15442Labels permutation346 hz
    mixedMoment B raw15442step0 raw15442step0Labels = mixedMoment B raw15442step1 raw15442step1Labels := by
      have ha : raw15442step1 = (fun i j => raw15442step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15442step1 raw15442step0; decide +kernel
      have hl : raw15442step1Labels = raw15442step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15442step0 raw15442step0Labels permutation146 permutation7
    mixedMoment B raw15442step1 raw15442step1Labels = mixedMoment B raw15442step2 raw15442step2Labels := by
      have ha : raw15442step2 = raw15442step1 := by apply Matrix.ext; unfold raw15442step2 raw15442step1; decide +kernel
      have hl : raw15442step1Labels = labelEmbedding1 ∘ raw15442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15442step1 raw15442step1Labels raw15442step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw15443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15443step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15443step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15443step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15443 raw15443Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw15443 raw15443Labels = mixedMoment B raw15443step0 raw15443step0Labels := by
      have hz : ∀ j, raw15443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15443step0 = (fun i j => raw15443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15443step0 raw15443; decide +kernel
      have hl : raw15443step0Labels = raw15443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15443 raw15443Labels permutation346 hz
    mixedMoment B raw15443step0 raw15443step0Labels = mixedMoment B raw15443step1 raw15443step1Labels := by
      have ha : raw15443step1 = (fun i j => raw15443step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15443step1 raw15443step0; decide +kernel
      have hl : raw15443step1Labels = raw15443step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15443step0 raw15443step0Labels permutation48 permutation5
    mixedMoment B raw15443step1 raw15443step1Labels = mixedMoment B raw15443step2 raw15443step2Labels := by
      have ha : raw15443step2 = -raw15443step1 := by apply Matrix.ext; change ∀ i j, raw15443step2 i j = -(raw15443step1 i j); unfold raw15443step2 raw15443step1; decide +kernel
      have hl : raw15443step2Labels = raw15443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15443step2 raw15443step2Labels = mixedMoment B raw15443step3 raw15443step3Labels := by
      have ha : raw15443step3 = raw15443step2 := by apply Matrix.ext; unfold raw15443step3 raw15443step2; decide +kernel
      have hl : raw15443step2Labels = labelEmbedding1 ∘ raw15443step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15443step2 raw15443step2Labels raw15443step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw15444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15444step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15444step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15444 raw15444Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw15444 raw15444Labels = mixedMoment B raw15444step0 raw15444step0Labels := by
      have hz : ∀ j, raw15444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15444step0 = (fun i j => raw15444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15444step0 raw15444; decide +kernel
      have hl : raw15444step0Labels = raw15444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15444 raw15444Labels permutation346 hz
    mixedMoment B raw15444step0 raw15444step0Labels = mixedMoment B raw15444step1 raw15444step1Labels := by
      have ha : raw15444step1 = (fun i j => raw15444step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15444step1 raw15444step0; decide +kernel
      have hl : raw15444step1Labels = raw15444step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15444step0 raw15444step0Labels permutation54 permutation5
    mixedMoment B raw15444step1 raw15444step1Labels = mixedMoment B raw15444step2 raw15444step2Labels := by
      have ha : raw15444step2 = -raw15444step1 := by apply Matrix.ext; change ∀ i j, raw15444step2 i j = -(raw15444step1 i j); unfold raw15444step2 raw15444step1; decide +kernel
      have hl : raw15444step2Labels = raw15444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15444step2 raw15444step2Labels = mixedMoment B raw15444step3 raw15444step3Labels := by
      have ha : raw15444step3 = raw15444step2 := by apply Matrix.ext; unfold raw15444step3 raw15444step2; decide +kernel
      have hl : raw15444step2Labels = labelEmbedding1 ∘ raw15444step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15444step2 raw15444step2Labels raw15444step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw15445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15445step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15445step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15445 raw15445Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw15445 raw15445Labels = mixedMoment B raw15445step0 raw15445step0Labels := by
      have ha : raw15445step0 = (fun i j => raw15445 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15445step0 raw15445; decide +kernel
      have hl : raw15445step0Labels = raw15445Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15445 raw15445Labels permutation168 permutation5
    mixedMoment B raw15445step0 raw15445step0Labels = mixedMoment B raw15445step1 raw15445step1Labels := by
      have ha : raw15445step1 = -raw15445step0 := by apply Matrix.ext; change ∀ i j, raw15445step1 i j = -(raw15445step0 i j); unfold raw15445step1 raw15445step0; decide +kernel
      have hl : raw15445step1Labels = raw15445step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15445step1 raw15445step1Labels = mixedMoment B raw15445step2 raw15445step2Labels := by
      have ha : raw15445step2 = raw15445step1 := by apply Matrix.ext; unfold raw15445step2 raw15445step1; decide +kernel
      have hl : raw15445step1Labels = labelEmbedding1 ∘ raw15445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15445step1 raw15445step1Labels raw15445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw15446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15446step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15446step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15446 raw15446Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw15446 raw15446Labels = mixedMoment B raw15446step0 raw15446step0Labels := by
      have ha : raw15446step0 = (fun i j => raw15446 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15446step0 raw15446; decide +kernel
      have hl : raw15446step0Labels = raw15446Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15446 raw15446Labels permutation168 permutation5
    mixedMoment B raw15446step0 raw15446step0Labels = mixedMoment B raw15446step1 raw15446step1Labels := by
      have ha : raw15446step1 = -raw15446step0 := by apply Matrix.ext; change ∀ i j, raw15446step1 i j = -(raw15446step0 i j); unfold raw15446step1 raw15446step0; decide +kernel
      have hl : raw15446step1Labels = raw15446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15446step1 raw15446step1Labels = mixedMoment B raw15446step2 raw15446step2Labels := by
      have ha : raw15446step2 = raw15446step1 := by apply Matrix.ext; unfold raw15446step2 raw15446step1; decide +kernel
      have hl : raw15446step1Labels = labelEmbedding1 ∘ raw15446step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15446step1 raw15446step1Labels raw15446step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw15447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15447step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15447 raw15447Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw15447 raw15447Labels = mixedMoment B raw15447step0 raw15447step0Labels := by
      have ha : raw15447step0 = (fun i j => raw15447 (permutation677 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15447step0 raw15447; decide +kernel
      have hl : raw15447step0Labels = raw15447Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15447 raw15447Labels permutation677 permutation7
    mixedMoment B raw15447step0 raw15447step0Labels = mixedMoment B raw15447step1 raw15447step1Labels := by
      have ha : raw15447step1 = raw15447step0 := by apply Matrix.ext; unfold raw15447step1 raw15447step0; decide +kernel
      have hl : raw15447step0Labels = labelEmbedding1 ∘ raw15447step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15447step0 raw15447step0Labels raw15447step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw15448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15448step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15448 raw15448Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw15448 raw15448Labels = mixedMoment B raw15448step0 raw15448step0Labels := by
      have ha : raw15448step0 = (fun i j => raw15448 (permutation228 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15448step0 raw15448; decide +kernel
      have hl : raw15448step0Labels = raw15448Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15448 raw15448Labels permutation228 permutation5
    mixedMoment B raw15448step0 raw15448step0Labels = mixedMoment B raw15448step1 raw15448step1Labels := by
      have ha : raw15448step1 = -raw15448step0 := by apply Matrix.ext; change ∀ i j, raw15448step1 i j = -(raw15448step0 i j); unfold raw15448step1 raw15448step0; decide +kernel
      have hl : raw15448step1Labels = raw15448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15448step1 raw15448step1Labels = mixedMoment B raw15448step2 raw15448step2Labels := by
      have ha : raw15448step2 = raw15448step1 := by apply Matrix.ext; unfold raw15448step2 raw15448step1; decide +kernel
      have hl : raw15448step1Labels = labelEmbedding1 ∘ raw15448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15448step1 raw15448step1Labels raw15448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw15449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15449step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15449step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15449 raw15449Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw15449 raw15449Labels = mixedMoment B raw15449step0 raw15449step0Labels := by
      have ha : raw15449step0 = (fun i j => raw15449 (permutation250 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15449step0 raw15449; decide +kernel
      have hl : raw15449step0Labels = raw15449Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15449 raw15449Labels permutation250 permutation5
    mixedMoment B raw15449step0 raw15449step0Labels = mixedMoment B raw15449step1 raw15449step1Labels := by
      have ha : raw15449step1 = -raw15449step0 := by apply Matrix.ext; change ∀ i j, raw15449step1 i j = -(raw15449step0 i j); unfold raw15449step1 raw15449step0; decide +kernel
      have hl : raw15449step1Labels = raw15449step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15449step1 raw15449step1Labels = mixedMoment B raw15449step2 raw15449step2Labels := by
      have ha : raw15449step2 = raw15449step1 := by apply Matrix.ext; unfold raw15449step2 raw15449step1; decide +kernel
      have hl : raw15449step1Labels = labelEmbedding1 ∘ raw15449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15449step1 raw15449step1Labels raw15449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw15450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw15450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw15450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw15450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15450 raw15450Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw15450 raw15450Labels = mixedMoment B raw15450step0 raw15450step0Labels := by
      have hz : ∀ j, raw15450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15450step0 = (fun i j => raw15450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15450step0 raw15450; decide +kernel
      have hl : raw15450step0Labels = raw15450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15450 raw15450Labels permutation346 hz
    mixedMoment B raw15450step0 raw15450step0Labels = mixedMoment B raw15450step1 raw15450step1Labels := by
      have ha : raw15450step1 = (fun i j => raw15450step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15450step1 raw15450step0; decide +kernel
      have hl : raw15450step1Labels = raw15450step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15450step0 raw15450step0Labels permutation35 permutation5
    mixedMoment B raw15450step1 raw15450step1Labels = mixedMoment B raw15450step2 raw15450step2Labels := by
      have ha : raw15450step2 = -raw15450step1 := by apply Matrix.ext; change ∀ i j, raw15450step2 i j = -(raw15450step1 i j); unfold raw15450step2 raw15450step1; decide +kernel
      have hl : raw15450step2Labels = raw15450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15450step2 raw15450step2Labels = mixedMoment B raw15450step3 raw15450step3Labels := by
      have ha : raw15450step3 = raw15450step2 := by apply Matrix.ext; unfold raw15450step3 raw15450step2; decide +kernel
      have hl : raw15450step2Labels = labelEmbedding1 ∘ raw15450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15450step2 raw15450step2Labels raw15450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw15451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15451 raw15451Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw15451 raw15451Labels = mixedMoment B raw15451step0 raw15451step0Labels := by
      have hz : ∀ j, raw15451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15451step0 = (fun i j => raw15451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15451step0 raw15451; decide +kernel
      have hl : raw15451step0Labels = raw15451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15451 raw15451Labels permutation346 hz
    mixedMoment B raw15451step0 raw15451step0Labels = mixedMoment B raw15451step1 raw15451step1Labels := by
      have ha : raw15451step1 = (fun i j => raw15451step0 (permutation103 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15451step1 raw15451step0; decide +kernel
      have hl : raw15451step1Labels = raw15451step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15451step0 raw15451step0Labels permutation103 permutation5
    mixedMoment B raw15451step1 raw15451step1Labels = mixedMoment B raw15451step2 raw15451step2Labels := by
      have ha : raw15451step2 = raw15451step1 := by apply Matrix.ext; unfold raw15451step2 raw15451step1; decide +kernel
      have hl : raw15451step1Labels = labelEmbedding1 ∘ raw15451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15451step1 raw15451step1Labels raw15451step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw15452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw15452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15452step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15452 raw15452Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw15452 raw15452Labels = mixedMoment B raw15452step0 raw15452step0Labels := by
      have ha : raw15452step0 = (fun i j => raw15452 (permutation517 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15452step0 raw15452; decide +kernel
      have hl : raw15452step0Labels = raw15452Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15452 raw15452Labels permutation517 permutation5
    mixedMoment B raw15452step0 raw15452step0Labels = mixedMoment B raw15452step1 raw15452step1Labels := by
      have ha : raw15452step1 = raw15452step0 := by apply Matrix.ext; unfold raw15452step1 raw15452step0; decide +kernel
      have hl : raw15452step0Labels = labelEmbedding1 ∘ raw15452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15452step0 raw15452step0Labels raw15452step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw15453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw15453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15453 raw15453Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw15453 raw15453Labels = mixedMoment B raw15453step0 raw15453step0Labels := by
      have hz : ∀ j, raw15453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15453step0 = (fun i j => raw15453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15453step0 raw15453; decide +kernel
      have hl : raw15453step0Labels = raw15453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15453 raw15453Labels permutation346 hz
    mixedMoment B raw15453step0 raw15453step0Labels = mixedMoment B raw15453step1 raw15453step1Labels := by
      have ha : raw15453step1 = (fun i j => raw15453step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15453step1 raw15453step0; decide +kernel
      have hl : raw15453step1Labels = raw15453step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15453step0 raw15453step0Labels permutation101 permutation5
    mixedMoment B raw15453step1 raw15453step1Labels = mixedMoment B raw15453step2 raw15453step2Labels := by
      have ha : raw15453step2 = raw15453step1 := by apply Matrix.ext; unfold raw15453step2 raw15453step1; decide +kernel
      have hl : raw15453step1Labels = labelEmbedding1 ∘ raw15453step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15453step1 raw15453step1Labels raw15453step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw15454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw15454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15454 raw15454Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw15454 raw15454Labels = mixedMoment B raw15454step0 raw15454step0Labels := by
      have hz : ∀ j, raw15454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15454step0 = (fun i j => raw15454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15454step0 raw15454; decide +kernel
      have hl : raw15454step0Labels = raw15454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15454 raw15454Labels permutation346 hz
    mixedMoment B raw15454step0 raw15454step0Labels = mixedMoment B raw15454step1 raw15454step1Labels := by
      have ha : raw15454step1 = (fun i j => raw15454step0 (permutation95 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15454step1 raw15454step0; decide +kernel
      have hl : raw15454step1Labels = raw15454step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15454step0 raw15454step0Labels permutation95 permutation5
    mixedMoment B raw15454step1 raw15454step1Labels = mixedMoment B raw15454step2 raw15454step2Labels := by
      have ha : raw15454step2 = raw15454step1 := by apply Matrix.ext; unfold raw15454step2 raw15454step1; decide +kernel
      have hl : raw15454step1Labels = labelEmbedding1 ∘ raw15454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15454step1 raw15454step1Labels raw15454step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw15455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15455step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15455step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15455step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15455step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15455 raw15455Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw15455 raw15455Labels = mixedMoment B raw15455step0 raw15455step0Labels := by
      have hz : ∀ j, raw15455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15455step0 = (fun i j => raw15455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15455step0 raw15455; decide +kernel
      have hl : raw15455step0Labels = raw15455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15455 raw15455Labels permutation346 hz
    mixedMoment B raw15455step0 raw15455step0Labels = mixedMoment B raw15455step1 raw15455step1Labels := by
      have ha : raw15455step1 = (fun i j => raw15455step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15455step1 raw15455step0; decide +kernel
      have hl : raw15455step1Labels = raw15455step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15455step0 raw15455step0Labels permutation37 permutation5
    mixedMoment B raw15455step1 raw15455step1Labels = mixedMoment B raw15455step2 raw15455step2Labels := by
      have ha : raw15455step2 = -raw15455step1 := by apply Matrix.ext; change ∀ i j, raw15455step2 i j = -(raw15455step1 i j); unfold raw15455step2 raw15455step1; decide +kernel
      have hl : raw15455step2Labels = raw15455step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15455step2 raw15455step2Labels = mixedMoment B raw15455step3 raw15455step3Labels := by
      have ha : raw15455step3 = raw15455step2 := by apply Matrix.ext; unfold raw15455step3 raw15455step2; decide +kernel
      have hl : raw15455step2Labels = labelEmbedding1 ∘ raw15455step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15455step2 raw15455step2Labels raw15455step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw15456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15456step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15456step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15456step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15456 raw15456Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw15456 raw15456Labels = mixedMoment B raw15456step0 raw15456step0Labels := by
      have hz : ∀ j, raw15456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15456step0 = (fun i j => raw15456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15456step0 raw15456; decide +kernel
      have hl : raw15456step0Labels = raw15456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15456 raw15456Labels permutation346 hz
    mixedMoment B raw15456step0 raw15456step0Labels = mixedMoment B raw15456step1 raw15456step1Labels := by
      have ha : raw15456step1 = (fun i j => raw15456step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15456step1 raw15456step0; decide +kernel
      have hl : raw15456step1Labels = raw15456step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15456step0 raw15456step0Labels permutation37 permutation5
    mixedMoment B raw15456step1 raw15456step1Labels = mixedMoment B raw15456step2 raw15456step2Labels := by
      have ha : raw15456step2 = -raw15456step1 := by apply Matrix.ext; change ∀ i j, raw15456step2 i j = -(raw15456step1 i j); unfold raw15456step2 raw15456step1; decide +kernel
      have hl : raw15456step2Labels = raw15456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15456step2 raw15456step2Labels = mixedMoment B raw15456step3 raw15456step3Labels := by
      have ha : raw15456step3 = raw15456step2 := by apply Matrix.ext; unfold raw15456step3 raw15456step2; decide +kernel
      have hl : raw15456step2Labels = labelEmbedding1 ∘ raw15456step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15456step2 raw15456step2Labels raw15456step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3772 node3772Labels := by rfl

def raw15457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15457step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15457 raw15457Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw15457 raw15457Labels = mixedMoment B raw15457step0 raw15457step0Labels := by
      have ha : raw15457step0 = (fun i j => raw15457 (permutation677 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15457step0 raw15457; decide +kernel
      have hl : raw15457step0Labels = raw15457Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15457 raw15457Labels permutation677 permutation7
    mixedMoment B raw15457step0 raw15457step0Labels = mixedMoment B raw15457step1 raw15457step1Labels := by
      have ha : raw15457step1 = raw15457step0 := by apply Matrix.ext; unfold raw15457step1 raw15457step0; decide +kernel
      have hl : raw15457step0Labels = labelEmbedding1 ∘ raw15457step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15457step0 raw15457step0Labels raw15457step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw15458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15458step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15458step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15458 raw15458Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw15458 raw15458Labels = mixedMoment B raw15458step0 raw15458step0Labels := by
      have hz : ∀ j, raw15458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15458step0 = (fun i j => raw15458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15458step0 raw15458; decide +kernel
      have hl : raw15458step0Labels = raw15458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15458 raw15458Labels permutation346 hz
    mixedMoment B raw15458step0 raw15458step0Labels = mixedMoment B raw15458step1 raw15458step1Labels := by
      have ha : raw15458step1 = (fun i j => raw15458step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15458step1 raw15458step0; decide +kernel
      have hl : raw15458step1Labels = raw15458step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15458step0 raw15458step0Labels permutation146 permutation7
    mixedMoment B raw15458step1 raw15458step1Labels = mixedMoment B raw15458step2 raw15458step2Labels := by
      have ha : raw15458step2 = raw15458step1 := by apply Matrix.ext; unfold raw15458step2 raw15458step1; decide +kernel
      have hl : raw15458step1Labels = labelEmbedding1 ∘ raw15458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15458step1 raw15458step1Labels raw15458step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw15459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw15459Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw15459step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15459step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15459step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15459step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15459step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15459step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15459 raw15459Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw15459 raw15459Labels = mixedMoment B raw15459step0 raw15459step0Labels := by
      have hz : ∀ j, raw15459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15459step0 = (fun i j => raw15459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15459step0 raw15459; decide +kernel
      have hl : raw15459step0Labels = raw15459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15459 raw15459Labels permutation346 hz
    mixedMoment B raw15459step0 raw15459step0Labels = mixedMoment B raw15459step1 raw15459step1Labels := by
      have ha : raw15459step1 = (fun i j => raw15459step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15459step1 raw15459step0; decide +kernel
      have hl : raw15459step1Labels = raw15459step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15459step0 raw15459step0Labels permutation51 permutation5
    mixedMoment B raw15459step1 raw15459step1Labels = mixedMoment B raw15459step2 raw15459step2Labels := by
      have ha : raw15459step2 = -raw15459step1 := by apply Matrix.ext; change ∀ i j, raw15459step2 i j = -(raw15459step1 i j); unfold raw15459step2 raw15459step1; decide +kernel
      have hl : raw15459step2Labels = raw15459step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15459step2 raw15459step2Labels = mixedMoment B raw15459step3 raw15459step3Labels := by
      have ha : raw15459step3 = raw15459step2 := by apply Matrix.ext; unfold raw15459step3 raw15459step2; decide +kernel
      have hl : raw15459step2Labels = labelEmbedding1 ∘ raw15459step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15459step2 raw15459step2Labels raw15459step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw15460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15460step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw15460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw15460step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw15460step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15460 raw15460Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw15460 raw15460Labels = mixedMoment B raw15460step0 raw15460step0Labels := by
      have hz : ∀ j, raw15460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15460step0 = (fun i j => raw15460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15460step0 raw15460; decide +kernel
      have hl : raw15460step0Labels = raw15460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15460 raw15460Labels permutation346 hz
    mixedMoment B raw15460step0 raw15460step0Labels = mixedMoment B raw15460step1 raw15460step1Labels := by
      have ha : raw15460step1 = (fun i j => raw15460step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15460step1 raw15460step0; decide +kernel
      have hl : raw15460step1Labels = raw15460step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15460step0 raw15460step0Labels permutation35 permutation5
    mixedMoment B raw15460step1 raw15460step1Labels = mixedMoment B raw15460step2 raw15460step2Labels := by
      have ha : raw15460step2 = -raw15460step1 := by apply Matrix.ext; change ∀ i j, raw15460step2 i j = -(raw15460step1 i j); unfold raw15460step2 raw15460step1; decide +kernel
      have hl : raw15460step2Labels = raw15460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15460step2 raw15460step2Labels = mixedMoment B raw15460step3 raw15460step3Labels := by
      have ha : raw15460step3 = raw15460step2 := by apply Matrix.ext; unfold raw15460step3 raw15460step2; decide +kernel
      have hl : raw15460step2Labels = labelEmbedding1 ∘ raw15460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15460step2 raw15460step2Labels raw15460step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw15461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15461Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15461step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15461step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15461 raw15461Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw15461 raw15461Labels = mixedMoment B raw15461step0 raw15461step0Labels := by
      have hz : ∀ j, raw15461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15461step0 = (fun i j => raw15461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15461step0 raw15461; decide +kernel
      have hl : raw15461step0Labels = raw15461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15461 raw15461Labels permutation346 hz
    mixedMoment B raw15461step0 raw15461step0Labels = mixedMoment B raw15461step1 raw15461step1Labels := by
      have ha : raw15461step1 = (fun i j => raw15461step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15461step1 raw15461step0; decide +kernel
      have hl : raw15461step1Labels = raw15461step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15461step0 raw15461step0Labels permutation146 permutation7
    mixedMoment B raw15461step1 raw15461step1Labels = mixedMoment B raw15461step2 raw15461step2Labels := by
      have ha : raw15461step2 = raw15461step1 := by apply Matrix.ext; unfold raw15461step2 raw15461step1; decide +kernel
      have hl : raw15461step1Labels = labelEmbedding1 ∘ raw15461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15461step1 raw15461step1Labels raw15461step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw15462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15462 raw15462Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw15462 raw15462Labels = mixedMoment B raw15462step0 raw15462step0Labels := by
      have ha : raw15462step0 = (fun i j => raw15462 (permutation677 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15462step0 raw15462; decide +kernel
      have hl : raw15462step0Labels = raw15462Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15462 raw15462Labels permutation677 permutation7
    mixedMoment B raw15462step0 raw15462step0Labels = mixedMoment B raw15462step1 raw15462step1Labels := by
      have ha : raw15462step1 = raw15462step0 := by apply Matrix.ext; unfold raw15462step1 raw15462step0; decide +kernel
      have hl : raw15462step0Labels = labelEmbedding1 ∘ raw15462step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15462step0 raw15462step0Labels raw15462step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw15463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15463Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw15463step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15463step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15463 raw15463Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw15463 raw15463Labels = mixedMoment B raw15463step0 raw15463step0Labels := by
      have hz : ∀ j, raw15463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15463step0 = (fun i j => raw15463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15463step0 raw15463; decide +kernel
      have hl : raw15463step0Labels = raw15463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15463 raw15463Labels permutation346 hz
    mixedMoment B raw15463step0 raw15463step0Labels = mixedMoment B raw15463step1 raw15463step1Labels := by
      have ha : raw15463step1 = (fun i j => raw15463step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15463step1 raw15463step0; decide +kernel
      have hl : raw15463step1Labels = raw15463step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15463step0 raw15463step0Labels permutation146 permutation7
    mixedMoment B raw15463step1 raw15463step1Labels = mixedMoment B raw15463step2 raw15463step2Labels := by
      have ha : raw15463step2 = raw15463step1 := by apply Matrix.ext; unfold raw15463step2 raw15463step1; decide +kernel
      have hl : raw15463step1Labels = labelEmbedding1 ∘ raw15463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15463step1 raw15463step1Labels raw15463step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

def raw15464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw15464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw15464step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15464step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15464 raw15464Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw15464 raw15464Labels = mixedMoment B raw15464step0 raw15464step0Labels := by
      have hz : ∀ j, raw15464 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15464step0 = (fun i j => raw15464 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15464step0 raw15464; decide +kernel
      have hl : raw15464step0Labels = raw15464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15464 raw15464Labels permutation346 hz
    mixedMoment B raw15464step0 raw15464step0Labels = mixedMoment B raw15464step1 raw15464step1Labels := by
      have ha : raw15464step1 = (fun i j => raw15464step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15464step1 raw15464step0; decide +kernel
      have hl : raw15464step1Labels = raw15464step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15464step0 raw15464step0Labels permutation146 permutation7
    mixedMoment B raw15464step1 raw15464step1Labels = mixedMoment B raw15464step2 raw15464step2Labels := by
      have ha : raw15464step2 = raw15464step1 := by apply Matrix.ext; unfold raw15464step2 raw15464step1; decide +kernel
      have hl : raw15464step1Labels = labelEmbedding1 ∘ raw15464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15464step1 raw15464step1Labels raw15464step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw15465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15465step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15465step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15465step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15465step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15465 raw15465Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw15465 raw15465Labels = mixedMoment B raw15465step0 raw15465step0Labels := by
      have ha : raw15465step0 = (fun i j => raw15465 (permutation296 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15465step0 raw15465; decide +kernel
      have hl : raw15465step0Labels = raw15465Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15465 raw15465Labels permutation296 permutation5
    mixedMoment B raw15465step0 raw15465step0Labels = mixedMoment B raw15465step1 raw15465step1Labels := by
      have ha : raw15465step1 = -raw15465step0 := by apply Matrix.ext; change ∀ i j, raw15465step1 i j = -(raw15465step0 i j); unfold raw15465step1 raw15465step0; decide +kernel
      have hl : raw15465step1Labels = raw15465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15465step1 raw15465step1Labels = mixedMoment B raw15465step2 raw15465step2Labels := by
      have ha : raw15465step2 = raw15465step1 := by apply Matrix.ext; unfold raw15465step2 raw15465step1; decide +kernel
      have hl : raw15465step1Labels = labelEmbedding8 ∘ raw15465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15465step1 raw15465step1Labels raw15465step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw15466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15466step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15466 raw15466Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw15466 raw15466Labels = mixedMoment B raw15466step0 raw15466step0Labels := by
      have ha : raw15466step0 = (fun i j => raw15466 (permutation527 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15466step0 raw15466; decide +kernel
      have hl : raw15466step0Labels = raw15466Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15466 raw15466Labels permutation527 permutation4
    mixedMoment B raw15466step0 raw15466step0Labels = mixedMoment B raw15466step1 raw15466step1Labels := by
      have ha : raw15466step1 = raw15466step0 := by apply Matrix.ext; unfold raw15466step1 raw15466step0; decide +kernel
      have hl : raw15466step0Labels = labelEmbedding7 ∘ raw15466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15466step0 raw15466step0Labels raw15466step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw15467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15467step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15467 raw15467Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw15467 raw15467Labels = mixedMoment B raw15467step0 raw15467step0Labels := by
      have ha : raw15467step0 = (fun i j => raw15467 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15467step0 raw15467; decide +kernel
      have hl : raw15467step0Labels = raw15467Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15467 raw15467Labels permutation526 permutation4
    mixedMoment B raw15467step0 raw15467step0Labels = mixedMoment B raw15467step1 raw15467step1Labels := by
      have ha : raw15467step1 = raw15467step0 := by apply Matrix.ext; unfold raw15467step1 raw15467step0; decide +kernel
      have hl : raw15467step0Labels = labelEmbedding7 ∘ raw15467step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15467step0 raw15467step0Labels raw15467step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw15468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15468step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15468step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15468step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15468 raw15468Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw15468 raw15468Labels = mixedMoment B raw15468step0 raw15468step0Labels := by
      have ha : raw15468step0 = (fun i j => raw15468 (permutation228 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15468step0 raw15468; decide +kernel
      have hl : raw15468step0Labels = raw15468Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15468 raw15468Labels permutation228 permutation6
    mixedMoment B raw15468step0 raw15468step0Labels = mixedMoment B raw15468step1 raw15468step1Labels := by
      have ha : raw15468step1 = -raw15468step0 := by apply Matrix.ext; change ∀ i j, raw15468step1 i j = -(raw15468step0 i j); unfold raw15468step1 raw15468step0; decide +kernel
      have hl : raw15468step1Labels = raw15468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15468step1 raw15468step1Labels = mixedMoment B raw15468step2 raw15468step2Labels := by
      have ha : raw15468step2 = raw15468step1 := by apply Matrix.ext; unfold raw15468step2 raw15468step1; decide +kernel
      have hl : raw15468step1Labels = labelEmbedding9 ∘ raw15468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15468step1 raw15468step1Labels raw15468step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw15469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15469step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15469 raw15469Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw15469 raw15469Labels = mixedMoment B raw15469step0 raw15469step0Labels := by
      have ha : raw15469step0 = (fun i j => raw15469 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15469step0 raw15469; decide +kernel
      have hl : raw15469step0Labels = raw15469Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15469 raw15469Labels permutation526 permutation4
    mixedMoment B raw15469step0 raw15469step0Labels = mixedMoment B raw15469step1 raw15469step1Labels := by
      have ha : raw15469step1 = raw15469step0 := by apply Matrix.ext; unfold raw15469step1 raw15469step0; decide +kernel
      have hl : raw15469step0Labels = labelEmbedding7 ∘ raw15469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15469step0 raw15469step0Labels raw15469step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw15470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15470 raw15470Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw15470 raw15470Labels = mixedMoment B raw15470step0 raw15470step0Labels := by
      have hz : ∀ j, raw15470 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw15470step0 = (fun i j => raw15470 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw15470step0 raw15470; decide +kernel
      have hl : raw15470step0Labels = raw15470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15470 raw15470Labels permutation265 hz
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw15471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15471step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15471 raw15471Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw15471 raw15471Labels = mixedMoment B raw15471step0 raw15471step0Labels := by
      have ha : raw15471step0 = (fun i j => raw15471 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15471step0 raw15471; decide +kernel
      have hl : raw15471step0Labels = raw15471Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15471 raw15471Labels permutation271 permutation3
    mixedMoment B raw15471step0 raw15471step0Labels = mixedMoment B raw15471step1 raw15471step1Labels := by
      have ha : raw15471step1 = raw15471step0 := by apply Matrix.ext; unfold raw15471step1 raw15471step0; decide +kernel
      have hl : raw15471step0Labels = labelEmbedding6 ∘ raw15471step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15471step0 raw15471step0Labels raw15471step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw15472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15472 raw15472Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw15472 raw15472Labels = mixedMoment B raw15472step0 raw15472step0Labels := by
      have ha : raw15472step0 = (fun i j => raw15472 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15472step0 raw15472; decide +kernel
      have hl : raw15472step0Labels = raw15472Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15472 raw15472Labels permutation160 permutation2
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw15473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15473 raw15473Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw15473 raw15473Labels = mixedMoment B raw15473step0 raw15473step0Labels := by
      have ha : raw15473step0 = (fun i j => raw15473 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15473step0 raw15473; decide +kernel
      have hl : raw15473step0Labels = raw15473Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15473 raw15473Labels permutation166 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw15474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15474 raw15474Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw15474 raw15474Labels = mixedMoment B raw15474step0 raw15474step0Labels := by
      have ha : raw15474step0 = (fun i j => raw15474 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15474step0 raw15474; decide +kernel
      have hl : raw15474step0Labels = raw15474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15474 raw15474Labels permutation160 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw15475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15475step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15475 raw15475Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw15475 raw15475Labels = mixedMoment B raw15475step0 raw15475step0Labels := by
      have ha : raw15475step0 = (fun i j => raw15475 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15475step0 raw15475; decide +kernel
      have hl : raw15475step0Labels = raw15475Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15475 raw15475Labels permutation265 permutation3
    mixedMoment B raw15475step0 raw15475step0Labels = mixedMoment B raw15475step1 raw15475step1Labels := by
      have ha : raw15475step1 = raw15475step0 := by apply Matrix.ext; unfold raw15475step1 raw15475step0; decide +kernel
      have hl : raw15475step0Labels = labelEmbedding6 ∘ raw15475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15475step0 raw15475step0Labels raw15475step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw15476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15476 raw15476Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw15476 raw15476Labels = mixedMoment B raw15476step0 raw15476step0Labels := by
      have ha : raw15476step0 = (fun i j => raw15476 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15476step0 raw15476; decide +kernel
      have hl : raw15476step0Labels = raw15476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15476 raw15476Labels permutation154 permutation2
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw15477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15477 raw15477Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw15477 raw15477Labels = mixedMoment B raw15477step0 raw15477step0Labels := by
      have ha : raw15477step0 = (fun i j => raw15477 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15477step0 raw15477; decide +kernel
      have hl : raw15477step0Labels = raw15477Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15477 raw15477Labels permutation164 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw15478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15478 raw15478Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw15478 raw15478Labels = mixedMoment B raw15478step0 raw15478step0Labels := by
      have ha : raw15478step0 = (fun i j => raw15478 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15478step0 raw15478; decide +kernel
      have hl : raw15478step0Labels = raw15478Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15478 raw15478Labels permutation154 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw15479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15479step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15479 raw15479Labels = mixedMoment B node5004 node5004Labels := by
  calc
    mixedMoment B raw15479 raw15479Labels = mixedMoment B raw15479step0 raw15479step0Labels := by
      have ha : raw15479step0 = (fun i j => raw15479 (permutation572 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15479step0 raw15479; decide +kernel
      have hl : raw15479step0Labels = raw15479Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15479 raw15479Labels permutation572 permutation5
    mixedMoment B raw15479step0 raw15479step0Labels = mixedMoment B raw15479step1 raw15479step1Labels := by
      have ha : raw15479step1 = raw15479step0 := by apply Matrix.ext; unfold raw15479step1 raw15479step0; decide +kernel
      have hl : raw15479step0Labels = labelEmbedding8 ∘ raw15479step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15479step0 raw15479step0Labels raw15479step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5004 node5004Labels := by rfl

def raw15480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15480step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15480 raw15480Labels = mixedMoment B node5005 node5005Labels := by
  calc
    mixedMoment B raw15480 raw15480Labels = mixedMoment B raw15480step0 raw15480step0Labels := by
      have ha : raw15480step0 = (fun i j => raw15480 (permutation573 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15480step0 raw15480; decide +kernel
      have hl : raw15480step0Labels = raw15480Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15480 raw15480Labels permutation573 permutation5
    mixedMoment B raw15480step0 raw15480step0Labels = mixedMoment B raw15480step1 raw15480step1Labels := by
      have ha : raw15480step1 = raw15480step0 := by apply Matrix.ext; unfold raw15480step1 raw15480step0; decide +kernel
      have hl : raw15480step0Labels = labelEmbedding8 ∘ raw15480step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15480step0 raw15480step0Labels raw15480step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5005 node5005Labels := by rfl

def raw15481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15481step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15481 raw15481Labels = mixedMoment B node5005 node5005Labels := by
  calc
    mixedMoment B raw15481 raw15481Labels = mixedMoment B raw15481step0 raw15481step0Labels := by
      have ha : raw15481step0 = (fun i j => raw15481 (permutation571 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15481step0 raw15481; decide +kernel
      have hl : raw15481step0Labels = raw15481Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15481 raw15481Labels permutation571 permutation5
    mixedMoment B raw15481step0 raw15481step0Labels = mixedMoment B raw15481step1 raw15481step1Labels := by
      have ha : raw15481step1 = raw15481step0 := by apply Matrix.ext; unfold raw15481step1 raw15481step0; decide +kernel
      have hl : raw15481step0Labels = labelEmbedding8 ∘ raw15481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15481step0 raw15481step0Labels raw15481step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5005 node5005Labels := by rfl

def raw15482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw15482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15482step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15482 raw15482Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw15482 raw15482Labels = mixedMoment B raw15482step0 raw15482step0Labels := by
      have ha : raw15482step0 = (fun i j => raw15482 (permutation572 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15482step0 raw15482; decide +kernel
      have hl : raw15482step0Labels = raw15482Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15482 raw15482Labels permutation572 permutation5
    mixedMoment B raw15482step0 raw15482step0Labels = mixedMoment B raw15482step1 raw15482step1Labels := by
      have ha : raw15482step1 = raw15482step0 := by apply Matrix.ext; unfold raw15482step1 raw15482step0; decide +kernel
      have hl : raw15482step0Labels = labelEmbedding8 ∘ raw15482step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15482step0 raw15482step0Labels raw15482step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw15483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15483step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15483step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15483step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15483 raw15483Labels = mixedMoment B node4993 node4993Labels := by
  calc
    mixedMoment B raw15483 raw15483Labels = mixedMoment B raw15483step0 raw15483step0Labels := by
      have ha : raw15483step0 = (fun i j => raw15483 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15483step0 raw15483; decide +kernel
      have hl : raw15483step0Labels = raw15483Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15483 raw15483Labels permutation681 permutation3
    mixedMoment B raw15483step0 raw15483step0Labels = mixedMoment B raw15483step1 raw15483step1Labels := by
      have ha : raw15483step1 = -raw15483step0 := by apply Matrix.ext; change ∀ i j, raw15483step1 i j = -(raw15483step0 i j); unfold raw15483step1 raw15483step0; decide +kernel
      have hl : raw15483step1Labels = raw15483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15483step1 raw15483step1Labels = mixedMoment B raw15483step2 raw15483step2Labels := by
      have ha : raw15483step2 = raw15483step1 := by apply Matrix.ext; unfold raw15483step2 raw15483step1; decide +kernel
      have hl : raw15483step1Labels = labelEmbedding6 ∘ raw15483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15483step1 raw15483step1Labels raw15483step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4993 node4993Labels := by rfl

def raw15484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15484step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15484step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15484 raw15484Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw15484 raw15484Labels = mixedMoment B raw15484step0 raw15484step0Labels := by
      have ha : raw15484step0 = (fun i j => raw15484 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15484step0 raw15484; decide +kernel
      have hl : raw15484step0Labels = raw15484Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15484 raw15484Labels permutation686 permutation3
    mixedMoment B raw15484step0 raw15484step0Labels = mixedMoment B raw15484step1 raw15484step1Labels := by
      have ha : raw15484step1 = -raw15484step0 := by apply Matrix.ext; change ∀ i j, raw15484step1 i j = -(raw15484step0 i j); unfold raw15484step1 raw15484step0; decide +kernel
      have hl : raw15484step1Labels = raw15484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15484step1 raw15484step1Labels = mixedMoment B raw15484step2 raw15484step2Labels := by
      have ha : raw15484step2 = raw15484step1 := by apply Matrix.ext; unfold raw15484step2 raw15484step1; decide +kernel
      have hl : raw15484step1Labels = labelEmbedding6 ∘ raw15484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15484step1 raw15484step1Labels raw15484step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

def raw15485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15485step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15485step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15485 raw15485Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw15485 raw15485Labels = mixedMoment B raw15485step0 raw15485step0Labels := by
      have ha : raw15485step0 = (fun i j => raw15485 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15485step0 raw15485; decide +kernel
      have hl : raw15485step0Labels = raw15485Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15485 raw15485Labels permutation680 permutation3
    mixedMoment B raw15485step0 raw15485step0Labels = mixedMoment B raw15485step1 raw15485step1Labels := by
      have ha : raw15485step1 = -raw15485step0 := by apply Matrix.ext; change ∀ i j, raw15485step1 i j = -(raw15485step0 i j); unfold raw15485step1 raw15485step0; decide +kernel
      have hl : raw15485step1Labels = raw15485step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15485step1 raw15485step1Labels = mixedMoment B raw15485step2 raw15485step2Labels := by
      have ha : raw15485step2 = raw15485step1 := by apply Matrix.ext; unfold raw15485step2 raw15485step1; decide +kernel
      have hl : raw15485step1Labels = labelEmbedding6 ∘ raw15485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15485step1 raw15485step1Labels raw15485step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

def raw15486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw15486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15486step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15486step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15486 raw15486Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw15486 raw15486Labels = mixedMoment B raw15486step0 raw15486step0Labels := by
      have ha : raw15486step0 = (fun i j => raw15486 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15486step0 raw15486; decide +kernel
      have hl : raw15486step0Labels = raw15486Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15486 raw15486Labels permutation682 permutation3
    mixedMoment B raw15486step0 raw15486step0Labels = mixedMoment B raw15486step1 raw15486step1Labels := by
      have ha : raw15486step1 = -raw15486step0 := by apply Matrix.ext; change ∀ i j, raw15486step1 i j = -(raw15486step0 i j); unfold raw15486step1 raw15486step0; decide +kernel
      have hl : raw15486step1Labels = raw15486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15486step1 raw15486step1Labels = mixedMoment B raw15486step2 raw15486step2Labels := by
      have ha : raw15486step2 = raw15486step1 := by apply Matrix.ext; unfold raw15486step2 raw15486step1; decide +kernel
      have hl : raw15486step1Labels = labelEmbedding6 ∘ raw15486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15486step1 raw15486step1Labels raw15486step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw15487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15487 raw15487Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw15487 raw15487Labels = mixedMoment B raw15487step0 raw15487step0Labels := by
      have ha : raw15487step0 = (fun i j => raw15487 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15487step0 raw15487; decide +kernel
      have hl : raw15487step0Labels = raw15487Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15487 raw15487Labels permutation265 permutation3
    _ = mixedMoment B node3869 node3869Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
